
// SPDX-License-Identifier: MIT
pragma solidity ^0.8;

import '/home/vagner/Secureum_Staking_Rewards/.certora_internal/23_03_15_15_48_29_870/.certora_sources/autoFinder_StakingRewards.sol';

contract StakingRewardsHarness is StakingRewards {
constructor(address _stakingToken, address _rewardToken) StakingRewards(_stakingToken, _rewardToken) {}

function rewardTransferTest(address user, uint amount) external {
    rewardsToken.transfer(user, amount);
}

function updateRewardHelper(address user) external updateReward(user){

}
}

