use crate::FastMap;
#[cfg(feature = "onchain")]
use crate::error::OnchainError;
use crate::math::tick_math::{MAX_TICK, MIN_TICK};
use crate::pool::swap::Slot0;
#[cfg(feature = "onchain")]
use alloy_primitives::BlockNumber;
#[cfg(feature = "onchain")]
use alloy_primitives::aliases::I24;
use alloy_primitives::{Address, U160, U256};
use std::marker::PhantomData;
use std::sync::Arc;

#[cfg(feature = "onchain")]
use alloy_provider::Provider;
#[cfg(feature = "onchain")]
use alloy_sol_macro::sol;

#[cfg(feature = "onchain")]
sol! {
    #[sol(rpc)]
    interface IV3Pool {
        function tickSpacing() external view returns (int24);
        function tickBitmap(int16 wordPosition) external view returns (uint256);
        function getReserves() external view returns (
            uint112 reserve0,
            uint112 reserve1,
            uint32 blockTimestampLast
        );
        function token0() external view returns (address);
        function token1() external view returns (address);
        function slot0() external view returns (
            uint160 sqrtPriceX96,
            int24 tick,
            uint16 observationIndex,
            uint16 observationCardinality,
            uint16 observationCardinalityNext,
            uint8 feeProtocol,
            bool unlocked
        );
        function liquidity() external view returns (uint128);
        function ticks(int24 tick) external view returns (uint128 liquidityGross, int128 liquidityNet);
    }
}

#[cfg(feature = "onchain")]
sol! {
    struct Call {
        address target;
        bytes callData;
    }

    #[sol(rpc)]
    interface IMulticall {
        function aggregate(Call[] calls)
            external
            view
            returns (uint256 blockNumber, bytes[] returnData);
    }
}

pub type OnchainProvider<P> = Arc<P>;

#[derive(Debug, Clone)]
pub struct TickInfo {
    pub word_position: i16,
    pub liquidity_gross: u128,
    pub liquidity_net: i128,
}

/// Converts an `Address` into its `U160` numeric representation.
///
/// This is mainly used to compare or sort addresses by value.
#[inline(always)]
pub fn address_to_u160(address: Address) -> U160 {
    address.into()
}

/// Returns the token pair sorted by numeric address, as used by Uniswap V3.
///
/// This is helpful when you want a canonical `(token0, token1)` ordering
/// regardless of input order.
pub fn sort_tokens(token0: Address, token1: Address) -> (Address, Address) {
    if address_to_u160(token0) < address_to_u160(token1) {
        (token0, token1)
    } else {
        (token1, token0)
    }
}

/// Computes the inclusive range of bitmap word indices that should be
/// scanned for initialized ticks around a current tick and spacing.
///
/// Use this before calling bitmap fetch APIs to limit on‑chain calls
/// to the relevant words for a given swap direction.
pub fn generate_search_range(current_tick: i32, tick_spacing: i32, zero_for_one: bool) -> Vec<i16> {
    let min_word: i16;
    let max_word: i16;

    if zero_for_one {
        let mut min_compressed = MIN_TICK / tick_spacing;

        if MIN_TICK % tick_spacing != 0 {
            min_compressed -= 1;
        }

        min_word = (min_compressed >> 8) as i16;

        let mut compressed = current_tick / tick_spacing;

        if current_tick < 0 && (current_tick % tick_spacing) != 0 {
            compressed -= 1;
        }
        max_word = (compressed >> 8) as i16;
    } else {
        let mut compressed = current_tick / tick_spacing;
        if current_tick < 0 && (current_tick % tick_spacing) != 0 {
            compressed -= 1;
        }
        min_word = (compressed >> 8) as i16;
        max_word = ((MAX_TICK / tick_spacing) >> 8) as i16;
    }

    (min_word..=max_word).collect()
}

#[derive(Clone, Debug)]
pub struct V3Pool<P> {
    pub pool_address: Address,
    pub token0: Address,
    pub token1: Address,
    pub fee_pips: u32,
    pub slot0: Slot0,
    pub liquidity: u128,
    pub tick_spacing: i32,
    pub bitmap: FastMap<i16, U256>,
    pub ticks: FastMap<i32, TickInfo>,
    _marker: PhantomData<P>,
    #[cfg(feature = "onchain")]
    pub contract: IV3Pool::IV3PoolInstance<OnchainProvider<P>>,
    #[cfg(feature = "onchain")]
    pub multicall: IMulticall::IMulticallInstance<OnchainProvider<P>>,
    // #[cfg(feature = "onchain")]
    // provider: OnchainProvider<P>,
}

impl<P> V3Pool<P> {
    /// Returns the net liquidity delta at a given tick, if it exists.
    ///
    /// This is used during swaps to update in‑range liquidity when
    /// crossing initialized ticks.
    pub fn get_liquidity_net(&self, tick: &i32) -> Option<i128> {
        self.ticks
            .get(tick)
            .map(|tick_info| tick_info.liquidity_net)
    }

    #[cfg(not(feature = "onchain"))]
    /// Constructs an in‑memory pool for pure math / simulation use,
    /// without attaching any on‑chain provider or contracts.
    ///
    /// You are expected to manually populate `slot0`, `liquidity`,
    /// `tick_spacing`, `bitmap`, and `ticks` as needed.
    pub fn new(pool_address: Address, token0: Address, token1: Address, fee_pips: u32) -> Self {
        let (token0, token1) = sort_tokens(token0, token1);

        Self {
            pool_address,
            token0,
            token1,
            fee_pips,
            slot0: Slot0::default(),
            liquidity: 0u128,
            tick_spacing: 0i32,
            bitmap: FastMap::default(),
            ticks: FastMap::default(),
            _marker: PhantomData,
        }
    }
}

#[cfg(feature = "onchain")]
impl<P> V3Pool<P>
where
    P: Provider + Send + Sync + 'static,
{
    /// Constructs a pool bound to an on‑chain provider and generated
    /// contract bindings, enabling all async fetch/update helpers.
    ///
    /// Use this when you want to read actual Uniswap V3 pool state
    /// via JSON‑RPC and then run the math locally.
    pub fn new(
        pool_address: Address,
        token0: Address,
        token1: Address,
        fee_pips: u32,
        provider: OnchainProvider<P>,
    ) -> Self {
        let (token0, token1) = sort_tokens(token0, token1);

        let contract = IV3Pool::IV3PoolInstance::new(pool_address, provider.clone());
        let multicall = IMulticall::IMulticallInstance::new(pool_address, provider.clone());

        Self {
            pool_address,
            token0,
            token1,
            fee_pips,
            slot0: Slot0::default(),
            liquidity: 0u128,
            tick_spacing: 0i32,
            bitmap: FastMap::default(),
            ticks: FastMap::default(),
            _marker: PhantomData,
            contract,
            multicall,
            // provider,
        }
    }

    /// Reads the `tickSpacing` from the on‑chain pool contract
    /// at the given optional block number.
    pub async fn fetch_tick_spacing(
        &self,
        block_number: Option<BlockNumber>,
    ) -> Result<i32, OnchainError> {
        let mut call = self.contract.tickSpacing();

        if let Some(bn) = block_number {
            call = call.block(bn.into());
        }

        let tick_spacing = call
            .call()
            .await
            .map_err(|e| OnchainError::FailedToGetTickSpacing(e.to_string()))?;

        Ok(tick_spacing.as_i32())
    }

    /// Fetches `tickSpacing` on‑chain and stores it on this pool
    /// instance, returning the updated value.
    pub async fn update_tick_spacing(
        &mut self,
        block_number: Option<BlockNumber>,
    ) -> Result<i32, OnchainError> {
        self.tick_spacing = self.fetch_tick_spacing(block_number).await?;

        Ok(self.tick_spacing)
    }

    /// Fetches the Uniswap V3 `slot0` struct (sqrt price and tick)
    /// from the on‑chain pool contract.
    pub async fn fetch_slot0(
        &self,
        block_number: Option<BlockNumber>,
    ) -> Result<Slot0, OnchainError> {
        let mut call = self.contract.slot0();

        if let Some(bn) = block_number {
            call = call.block(bn.into());
        }

        let slot0 = call
            .call()
            .await
            .map_err(|e| OnchainError::FailedToGetSlot0(e.to_string()))?;

        Ok(Slot0 {
            sqrt_price_x96: U256::from(slot0.sqrtPriceX96),
            tick: slot0.tick.as_i32(),
        })
    }

    /// Fetches `slot0` on‑chain and stores it on this pool instance,
    /// returning the updated `Slot0`.
    pub async fn update_slot0(
        &mut self,
        block_number: Option<BlockNumber>,
    ) -> Result<Slot0, OnchainError> {
        self.slot0 = self.fetch_slot0(block_number).await?;
        Ok(self.slot0)
    }

    /// Fetches the current pool liquidity from the on‑chain contract
    /// at the given optional block number.
    pub async fn fetch_liquidity(
        &self,
        block_number: Option<BlockNumber>,
    ) -> Result<u128, OnchainError> {
        let mut call = self.contract.liquidity();

        if let Some(bn) = block_number {
            call = call.block(bn.into());
        }

        let liquidity = call
            .call()
            .await
            .map_err(|e| OnchainError::FailedToGetLiquidity(e.to_string()))?;
        Ok(liquidity)
    }

    /// Fetches liquidity on‑chain, stores it on this pool instance,
    /// and returns the updated value.
    pub async fn get_liquidity(
        &mut self,
        block_number: Option<BlockNumber>,
    ) -> Result<u128, OnchainError> {
        self.liquidity = self.fetch_liquidity(block_number).await?;

        Ok(self.liquidity)
    }

    pub async fn get_liquidity_latest(&mut self) -> Result<u128, OnchainError> {
        self.get_liquidity(None).await
    }

    /// Fetches `slot0` at the latest block and updates this pool.
    pub async fn update_slot0_latest(&mut self) -> Result<Slot0, OnchainError> {
        self.update_slot0(None).await
    }

    /// Fetches `tickSpacing` at the latest block and updates this pool.
    pub async fn update_tick_spacing_latest(&mut self) -> Result<i32, OnchainError> {
        self.update_tick_spacing(None).await
    }

    /// Convenience helper that fetches liquidity, `slot0`, and
    /// `tickSpacing` at the latest block and updates this pool.
    pub async fn refresh_latest(&mut self) -> Result<(), OnchainError> {
        let liq = self.fetch_liquidity(None).await?;
        let slot0 = self.fetch_slot0(None).await?;
        let spacing = self.fetch_tick_spacing(None).await?;

        self.liquidity = liq;
        self.slot0 = slot0;
        self.tick_spacing = spacing;

        Ok(())
    }

    /// Same as `refresh_latest`, but allows specifying a historical
    /// block number to read pool state from the past.
    pub async fn refresh(&mut self, block_number: Option<BlockNumber>) -> Result<(), OnchainError> {
        let liq = self.fetch_liquidity(block_number).await?;
        let slot0 = self.fetch_slot0(block_number).await?;
        let spacing = self.fetch_tick_spacing(block_number).await?;

        self.liquidity = liq;
        self.slot0 = slot0;
        self.tick_spacing = spacing;

        Ok(())
    }

    /// Uses a multicall contract to fetch tick bitmap words for the
    /// given word positions, optionally at a specific block number.
    ///
    /// Returns a sparse map from word index to non‑zero bitmap.
    pub async fn fetch_batch_bitmaps(
        &self,
        word_positions: &[i16],
        block_number: Option<BlockNumber>,
    ) -> Result<FastMap<i16, U256>, OnchainError> {
        let mut bitmap_calls: Vec<Call> = Vec::with_capacity(word_positions.len());

        for wp in word_positions {
            let call_data = self.contract.tickBitmap(*wp).calldata().to_owned();
            bitmap_calls.push(Call {
                target: self.pool_address,
                callData: call_data,
            });
        }

        let mut agg = self.multicall.aggregate(bitmap_calls);

        if let Some(bn) = block_number {
            agg = agg.block(bn.into());
        }
        let bitmap_data = agg
            .call()
            .await
            .map_err(|e| OnchainError::FailedToCallMulticall(e.to_string()))?;

        let mut bitmaps: FastMap<i16, U256> = FastMap::with_capacity(word_positions.len());

        for (i, raw) in bitmap_data.returnData.into_iter().enumerate() {
            let decoded = self
                .contract
                .tickBitmap(word_positions[i])
                .decode_output(raw)
                .map_err(|e| OnchainError::FailedToDecodeBitmap(e.to_string()))?;

            let bitmap = U256::from(decoded);

            if !bitmap.is_zero() {
                bitmaps.insert(word_positions[i], bitmap);
            }
        }

        Ok(bitmaps)
    }

    /// For each non‑zero bitmap word, decodes per‑tick liquidity from
    /// the on‑chain pool contract using a batched multicall.
    ///
    /// Returns a map from tick index to `TickInfo`.
    pub async fn fetch_ticks_for_bitmaps(
        &self,
        word_positions: &[i16],
        bitmaps: &FastMap<i16, U256>,
        block_number: Option<BlockNumber>,
    ) -> Result<FastMap<i32, TickInfo>, OnchainError> {
        let hint = word_positions.len().saturating_mul(6);
        let mut tick_calls: Vec<Call> = Vec::with_capacity(hint);
        let mut tick_indices: Vec<i32> = Vec::with_capacity(hint);
        let mut tick_word_positions: Vec<i16> = Vec::with_capacity(hint);

        for &wp in word_positions {
            if let Some(bitmap) = bitmaps.get(&wp) {
                for bit in 0..256 {
                    // Check if bit is set
                    if (*bitmap & (U256::ONE << bit)) == U256::ZERO {
                        continue;
                    }

                    let compressed: i32 = (wp as i32) * 256 + bit;
                    let tick_index: i32 = compressed * self.tick_spacing;

                    tick_indices.push(tick_index);
                    tick_word_positions.push(wp);

                    let call_data = self
                        .contract
                        .ticks(I24::try_from(tick_index).unwrap())
                        .calldata()
                        .to_owned();
                    tick_calls.push(Call {
                        target: self.pool_address,
                        callData: call_data,
                    });
                }
            }
        }

        // nothing initialized – early exit
        if tick_calls.is_empty() {
            return Ok(FastMap::default());
        }

        let mut agg = self.multicall.aggregate(tick_calls);

        if let Some(bn) = block_number {
            agg = agg.block(bn.into());
        }

        let return_data = agg
            .call()
            .await
            .map_err(|e| OnchainError::FailedToCallMulticall(e.to_string()))?;

        let mut ticks: FastMap<i32, TickInfo> = FastMap::with_capacity(tick_indices.len());

        for (i, raw) in return_data.returnData.into_iter().enumerate() {
            let tick_index = tick_indices[i];
            let wp = tick_word_positions[i];

            let decoded = self
                .contract
                .ticks(I24::try_from(tick_index).unwrap())
                .decode_output(raw)
                .map_err(|e| OnchainError::FailedToDecodeTick(e.to_string()))?;

            let liquidity_gross = decoded.liquidityGross;
            let liquidity_net = decoded.liquidityNet;

            if liquidity_gross != 0 {
                ticks.insert(
                    tick_index,
                    TickInfo {
                        word_position: wp,
                        liquidity_gross,
                        liquidity_net,
                    },
                );
            }
        }

        Ok(ticks)
    }

    /// Convenience wrapper that fetches both bitmaps and ticks for the
    /// given word positions in a single high‑level call.
    pub async fn fetch_bitmaps_and_ticks(
        &self,
        word_positions: &[i16],
        block_number: Option<BlockNumber>,
    ) -> Result<(FastMap<i16, U256>, FastMap<i32, TickInfo>), OnchainError> {
        // 1) fetch bitmaps
        let bitmaps = self
            .fetch_batch_bitmaps(word_positions, block_number)
            .await?;

        // 2) fetch per-tick liquidity for initialized bits
        let ticks = self
            .fetch_ticks_for_bitmaps(word_positions, &bitmaps, block_number)
            .await?;

        Ok((bitmaps, ticks))
    }

    /// Fetches and stores bitmaps and ticks for the given word
    /// positions, optionally at a specific block.
    pub async fn update_bitmaps_and_ticks(
        &mut self,
        word_positions: &[i16],
        block_number: Option<BlockNumber>,
    ) -> Result<(), OnchainError> {
        let (bitmaps, ticks) = self
            .fetch_bitmaps_and_ticks(word_positions, block_number)
            .await?;

        self.bitmap = bitmaps;
        self.ticks = ticks;

        Ok(())
    }

    /// Fetches and stores bitmaps and ticks for the given word
    /// positions at the latest block.
    pub async fn update_bitmaps_and_ticks_latest(
        &mut self,
        word_positions: &[i16],
    ) -> Result<(), OnchainError> {
        let (bitmaps, ticks) = self.fetch_bitmaps_and_ticks(word_positions, None).await?;

        self.bitmap = bitmaps;
        self.ticks = ticks;

        Ok(())
    }
}

#[cfg(all(test, feature = "onchain"))]
mod tests {
    use super::*;
    use alloy_primitives::address;
    use alloy_provider::transport::mock::Asserter;
    use alloy_provider::{Provider, ProviderBuilder};

    // mock provider for tests
    pub fn mock_provider() -> Arc<impl Provider> {
        let asserter = Asserter::new();
        let provider = ProviderBuilder::new().connect_mocked_client(asserter.clone());
        let provider = Arc::new(provider);
        provider
    }

    // --- Pure helpers: address_to_u160 & sort_tokens -----------------------------

    #[test]
    fn address_to_u160_roundtrip_like() {
        let addr = address!("0x123400000000000000000000000000000000abcd");
        let as_u160: U160 = address_to_u160(addr);

        // Converting back should give the same low 20 bytes
        let back: Address = Address::from(as_u160);
        assert_eq!(addr, back);
    }

    #[test]
    fn sort_tokens_orders_by_numeric_value() {
        let a = address!("0x0000000000000000000000000000000000000001");
        let b = address!("0x0000000000000000000000000000000000000002");

        // already sorted
        let (t0, t1) = sort_tokens(a, b);
        assert_eq!(t0, a);
        assert_eq!(t1, b);

        // reversed input still sorts
        let (t0, t1) = sort_tokens(b, a);
        assert_eq!(t0, a);
        assert_eq!(t1, b);
    }

    #[test]
    fn sort_tokens_handles_equal_addresses() {
        let a = address!("0x0000000000000000000000000000000000000001");
        let (t0, t1) = sort_tokens(a, a);

        // With equal addresses, result must still be the same pair (a, a)
        assert_eq!(t0, a);
        assert_eq!(t1, a);
    }

    // --- generate_search_range ---------------------------------------------------

    #[test]
    fn generate_search_range_is_symmetric_and_contiguous() {
        let current_tick: i32 = 13;
        let tick_spacing: i32 = 10;
        let zero_for_one: bool = false;

        let range = generate_search_range(current_tick, tick_spacing, zero_for_one);

        assert_eq!(range.len(), 347);

        assert_eq!(*range.first().unwrap(), 0);
        assert_eq!(*range.last().unwrap(), 346);
    }
    // --- V3Pool::new ------------------------------------------------------------

    #[test]
    fn v3pool_new_sorts_token_addresses_and_initializes_state() {
        let pool_address = address!("0x1000000000000000000000000000000000000000");
        let token_hi = address!("0x0000000000000000000000000000000000000002");
        let token_lo = address!("0x0000000000000000000000000000000000000001");

        let pool = V3Pool::new(pool_address, token_hi, token_lo, 3000, mock_provider());

        // basic field checks
        assert_eq!(pool.pool_address, pool_address);
        // token0/token1 sorted numerically, regardless of input order
        assert_eq!(pool.token0, token_lo);
        assert_eq!(pool.token1, token_hi);
        assert_eq!(pool.fee_pips, 3000);

        // initial state
        assert_eq!(pool.liquidity, 0);
        assert_eq!(pool.tick_spacing, 0);
        assert_eq!(pool.slot0.sqrt_price_x96, U256::ZERO);
        assert_eq!(pool.slot0.tick, 0);
        assert_eq!(pool.bitmap, FastMap::default());
    }
}
