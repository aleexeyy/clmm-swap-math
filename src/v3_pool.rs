use crate::error::OnchainError;
use crate::swap::Slot0;
use alloy::providers::Provider;
use alloy::sol;
use alloy_primitives::{Address, BlockNumber, U160, U256};
use futures::try_join;
use std::sync::Arc;

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
    }
}

pub type OnchainProvider<P> = Arc<P>;

pub fn address_to_u160(address: Address) -> U160 {
    address.into()
}

pub fn sort_tokens(token0: Address, token1: Address) -> (Address, Address) {
    if address_to_u160(token0) < address_to_u160(token1) {
        (token0, token1)
    } else {
        (token1, token0)
    }
}

struct V3Pool<P: Provider> {
    pub pool_address: Address,
    pub token0: Address,
    pub token1: Address,
    pub fee_pips: u32,
    pub slot0: Slot0,
    pub liquidity: u128,
    pub tick_spacing: i32,
    pub contract: IV3Pool::IV3PoolInstance<OnchainProvider<P>>,
    provider: OnchainProvider<P>,
}

impl<P: Provider + Send + Sync + 'static> V3Pool<P> {
    pub fn new(
        pool_address: Address,
        token0: Address,
        token1: Address,
        fee_pips: u32,
        provider: OnchainProvider<P>,
    ) -> Self {
        let (token0, token1) = sort_tokens(token0, token1);
        let contract = IV3Pool::IV3PoolInstance::new(pool_address, provider.clone());
        Self {
            pool_address,
            token0,
            token1,
            fee_pips,
            slot0: Slot0::default(),
            liquidity: 0u128,
            tick_spacing: 0i32,
            contract,
            provider,
        }
    }

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
    pub async fn update_tick_spacing(
        &mut self,
        block_number: Option<BlockNumber>,
    ) -> Result<i32, OnchainError> {
        self.tick_spacing = self.fetch_tick_spacing(block_number).await?;

        Ok(self.tick_spacing)
    }

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

    pub async fn update_slot0(
        &mut self,
        block_number: Option<BlockNumber>,
    ) -> Result<Slot0, OnchainError> {
        self.slot0 = self.fetch_slot0(block_number).await?;
        Ok(self.slot0)
    }

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

    pub async fn update_slot0_latest(&mut self) -> Result<Slot0, OnchainError> {
        self.update_slot0(None).await
    }

    pub async fn update_tick_spacing_latest(&mut self) -> Result<i32, OnchainError> {
        self.update_tick_spacing(None).await
    }

    pub async fn update_all_latest(&mut self) -> Result<(), OnchainError> {
        let (liq, slot0, spacing) = try_join!(
            self.fetch_liquidity(None),
            self.fetch_slot0(None),
            self.fetch_tick_spacing(None),
        )?;

        self.liquidity = liq;
        self.slot0 = slot0;
        self.tick_spacing = spacing;

        Ok(())
    }

    pub async fn update_all(
        &mut self,
        block_number: Option<BlockNumber>,
    ) -> Result<(), OnchainError> {
        let (liq, slot0, spacing) = try_join!(
            self.fetch_liquidity(block_number),
            self.fetch_slot0(block_number),
            self.fetch_tick_spacing(block_number),
        )?;

        self.liquidity = liq;
        self.slot0 = slot0;
        self.tick_spacing = spacing;

        Ok(())
    }
}
