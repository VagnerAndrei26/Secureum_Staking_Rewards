# if test -n "$1"
# then
#     RULE="--rule $1"
# fi
certoraRun ./harness/StakingRewardsHarness.sol:StakingRewardsHarness \
            ./DummyERC20A.sol \
            ./DummyERC20B.sol \
--verify StakingRewardsHarness:spec/StakingRewards.spec \
\
--link StakingRewardsHarness:stakingToken=DummyERC20A \
--link StakingRewardsHarness:rewardsToken=DummyERC20B \
\
\
\
--send_only \
--rule_sanity basic \
--msg "$1" \
