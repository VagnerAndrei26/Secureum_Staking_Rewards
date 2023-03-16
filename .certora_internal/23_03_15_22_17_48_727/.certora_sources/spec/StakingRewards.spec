import "./erc20.spec"

using DummyERC20A as stakingToken
using DummyERC20B as rewardsToken
/**************************************************
 *              METHODS DECLARATIONS              *
 **************************************************/
methods{
    stakingToken()                  returns (address)   envfree
    rewardsToken()                  returns (address)   envfree
    owner()                         returns (address)   envfree
    duration()                      returns (uint256)   envfree
    finishAt()                      returns (uint256)   envfree
    updatedAt()                     returns (uint256)   envfree
    rewardRate()                    returns (uint256)   envfree
    rewardPerTokenStored()          returns (uint256)   envfree
    userRewardPerTokenPaid(address) returns (uint256)   envfree
    rewards(address)                returns (uint256)   envfree
    totalSupply()                   returns (uint256)   envfree
    balanceOf(address)              returns (uint256)   envfree
    _min(uint256, uint256)          returns(uint256)    envfree
    rewardsToken.balanceOf(address) returns (uint256)   envfree
    stakingToken.balanceOf(address) returns (uint256)   envfree
    lastTimeRewardApplicable()      returns (uint256)
    rewardPerToken()                returns (uint256)
    earned(address)                 returns uint256
    stake(uint256)
    withdraw(uint256)
    getReward(address)
    setRewardsDuration(uint256)
    notifyRewardAmount(uint256)
}


//Setup
function firstSetup(env e, address user) {
    require user != currentContract && user != 0 && e.msg.sender == user;
}

function secondSetup(env e) {
    require e.msg.sender != currentContract;
    require e.msg.sender != 0;
    requireInvariant sumOfBalancesIsEQToTotalSupply;
}

//Ghost and hook
ghost mathint sumOfBalances {
    init_state axiom sumOfBalances == 0;
}

hook Sstore balanceOf[KEY address addy] uint256 balance (uint256 oldBalance) STORAGE {
    sumOfBalances = sumOfBalances + balance - oldBalance;
}

hook Sload uint256 val balanceOf[KEY address addy] STORAGE {
    require sumOfBalances >= val;
}


//Invariant 
//Total supply should be equal to the sum of all the balances
invariant sumOfBalancesIsEQToTotalSupply()
    totalSupply() == sumOfBalances


rule sanity(env e, method f){
    calldataarg args;
    f(e,args);
    assert false;
}
/**************************************************
 *              Valid State                       *
 **************************************************/
//stakingToken.balanceOf(currentContract) is 0 then totalSupply is 0
invariant totalSupplyToBalanceOfIs0()
    stakingToken.balanceOf(currentContract) == 0 => totalSupply() == 0
    {
        preserved with(env e){
            require e.msg.sender != currentContract;
            require totalSupply() == stakingToken.balanceOf(currentContract);
        }
    }

//stakingToken.balanceOf(currentContract) is greater than 0 then totalSupply is greater than 0
invariant totalSupplyToBalanceOfIsGT0()
    stakingToken.balanceOf(currentContract) > 0 => totalSupply() > 0
    {
        preserved with(env e){
            require e.msg.sender != currentContract;
            require totalSupply() == stakingToken.balanceOf(currentContract);
        }
    }



/**************************************************
 *              Variable transition                *
 **************************************************/
//Total supply can change only on stake and withdraw
rule changeTotalSupplyOnlyOnSomeMethods(env e, method f) {
    uint256 totalSupplyBefore = totalSupply();
    require e.msg.sender != currentContract;
    calldataarg args;
    f(e,args);
    uint256 totalSupplyAfter = totalSupply();
    
    assert totalSupplyBefore < totalSupplyAfter <=> f.selector == stake(uint256).selector, "Total Supply increased on another method than stake";
    assert totalSupplyBefore > totalSupplyAfter <=> f.selector == withdraw(uint256).selector, "Total Supply decreased on another method than withdraw";
}

//BalanceOf(user) should increase only on stake() and decrease only on withdraw()
rule changeBalanceOfUserOnSomeMethods(env e, address user) {
    uint256 balanceUserBefore = balanceOf(user);
    require user == e.msg.sender;
    method f;
    calldataarg args;
    f(e, args);
    uint256 balanceUserAfter = balanceOf(user);

    assert balanceUserBefore < balanceUserAfter <=> f.selector == stake(uint256).selector, "BalanceOf(user) increased on other method than stake";
    assert balanceUserBefore > balanceUserAfter <=> f.selector == withdraw(uint256).selector ,"BalanceOf(user) decreased on other method than withdraw";
}

//Updating of rewards for user must work if condition are met and should be modified on some methods
rule rewardsUpdatedAndModified(env e,method f, address user) {
    firstSetup(e,user);
    uint256 rewardsBefore = rewards(user);
    uint256 tokensBalanceBefore = balanceOf(user);
    calldataarg args;
    f(e,args);
    uint256 rewardsAfter = rewards(user);
    assert rewardsBefore != rewardsAfter => (f.selector == stake(uint256).selector || 
    f.selector == withdraw(uint256).selector ||
    f.selector == getReward().selector ||
    f.selector == updateRewardHelper(address).selector) , "Updating of rewards failed or it was modified by other methods than the specified ones";
    assert rewardsAfter > rewardsBefore => (updatedAt() <= finishAt() && tokensBalanceBefore > 0), "Rewards increased without meeting the conditions";
}

//User get the correct amount of reward tokens
rule userGetCorrectAmounOfRewardTokens(env e, address user) {
    firstSetup(e,user);
    uint256 rewardTokensAmountUserBefore = rewardsToken.balanceOf(user);
    uint256 rewardsUser = rewards(user);
    getReward(e);
    uint256 rewardTokensAmountUserAfter = rewardsToken.balanceOf(user);

    assert rewardTokensAmountUserAfter >= rewardTokensAmountUserBefore + rewardsUser, "User didnt get the correct amount of reward tokens";

}

//FinishAt, updateAt, rewardPerTokenStored and userRewardPerTokenPain shouldn't decrease
rule nonDecreasingVariables(method f, address user) {
    env e1; 
    env e2; 
    calldataarg args1; 
    calldataarg args2;

    require e1.block.timestamp < e2.block.timestamp;
    secondSetup(e1);
    secondSetup(e2);

    f(e1, args1);

    uint256 userRewardPerTokenPaidBefore = userRewardPerTokenPaid(user);
    uint256 rewardPerTokenStoredBefore = rewardPerTokenStored();
    uint256 updatedAtBefore = updatedAt();
    uint256 finishAtBefore = finishAt();

    f(e2, args2);

    uint256 userRewardPerTokenPaidAfter = userRewardPerTokenPaid(user);
    uint256 rewardPerTokenStoredAfter = rewardPerTokenStored();
    uint256 updatedAtAfter = updatedAt();
    uint256 finishAtAfter = finishAt();

    assert finishAtAfter >= finishAtBefore, "finishAt should not decrease";
    assert updatedAtAfter >= updatedAtBefore, "updatedAt should not decrease";
    assert rewardPerTokenStoredAfter >= rewardPerTokenStoredBefore, "rewardPerTokenStored should not decrease";
    assert userRewardPerTokenPaidAfter >= userRewardPerTokenPaidBefore, "userRewardPerTokenPaid[user] should not decrease";
}


/**************************************************
 *              High-level                        *
 **************************************************/

//Rewards should never decrease if getRewards was not called
rule rewardsShouldntDecrease(env e, address user) {
    method f;
    calldataarg args;
    firstSetup(e, user);
    require rewards(user) > 0;
    uint256 amountEarnedBefore = rewards(user);
    f(e,args);
    uint256 amountEarnedAfter = rewards(user);

 
    assert amountEarnedBefore > amountEarnedAfter <=> f.selector == getReward().selector, "Rewards decreased on other methods than getRewards";
}

//User should always be able to unstake after staking tokens
rule userCanAlwaysUnstakeAfterStake(env e, address user, uint256 amount) {
    firstSetup(e, user);
    stake(e,amount);
    uint256 amountBeforeWithdraw = stakingToken.balanceOf(user);
    withdraw(e,amount);
    uint256 amountAfterWithdraw = stakingToken.balanceOf(user);

    assert amountAfterWithdraw == amountBeforeWithdraw + amount, "User should be able always to unstake after staking tokens and get the same amount of tokens staked";
}

//The more a user has staked the more rewards should get
rule moreStakeMoreRewards(address user1, address user2) {
    env e; 
    storage initial = lastStorage;

    secondSetup(e);

    require user1 != 0 && user2 != 0;
    // Both users have last updated their rewards at the same time
    require userRewardPerTokenPaid(user1) == userRewardPerTokenPaid(user2);

    uint256 user1RewardsBefore = rewards(user1);
    uint256 user2RewardsBefore = rewards(user2);
    uint256 user1Balance = balanceOf(user1);
    uint256 user2Balance = balanceOf(user2);

    updateRewardHelper(e, user1);
    uint256 user1RewardsAfter = rewards(user1);

    updateRewardHelper(e, user2) at initial;
    uint256 user2RewardsAfter = rewards(user2);

    
    assert (user1RewardsAfter - user1RewardsBefore < user2RewardsAfter - user2RewardsBefore) =>
           (user1Balance < user2Balance),
           "User with more stake must get more rewards";
}


/**************************************************
 *              Unit-test                         *
 **************************************************/

//Integrity of stake
rule integrityOfStake(env e, address user) {
    uint256 amount;
    firstSetup(e, user);
    uint256 balanceOfUserBefore = balanceOf(user);
    uint256 totalSupplyBefore = totalSupply();
    uint256 tokenAmountBefore = stakingToken.balanceOf(currentContract);
    stake(e,amount);
    uint256 balanceOfUserAfter = balanceOf(user);
    uint256 totalSupplyAfter = totalSupply();
    uint256 tokenAmountAfter = stakingToken.balanceOf(currentContract);

    assert balanceOfUserAfter == balanceOfUserBefore + amount, "Balance didn't change correctly";
    assert totalSupplyAfter == totalSupplyBefore + amount, "TotalSupply didn't change correctly";
    assert tokenAmountAfter == tokenAmountBefore + amount, "The transferFrom failed";
}

//Integrity of withdraw
rule integrityOfWithdraw(env e, address user) {
    uint256 amount;
    firstSetup(e, user);
    uint256 balanceOfUserBefore = balanceOf(user);
    uint256 totalSupplyBefore = totalSupply();
    uint256 tokenAmountBefore = stakingToken.balanceOf(currentContract);
    withdraw(e,amount);
    uint256 balanceOfUserAfter = balanceOf(user);
    uint256 totalSupplyAfter = totalSupply();
    uint256 tokenAmountAfter = stakingToken.balanceOf(currentContract);

    assert balanceOfUserAfter == balanceOfUserBefore - amount, "Balance didn't change correctly";
    assert totalSupplyAfter == totalSupplyBefore - amount, "TotalSupply didn't change correctly";
    assert tokenAmountAfter == tokenAmountBefore - amount, "The transfer failed";
}

//Integrity of getRewards
rule integrityOfGetRewards(env e, address user) {
    firstSetup(e, user);
    uint256 rewardsBefore = rewards(user);
    uint256 rewardsTokenBefore = rewardsToken.balanceOf(user);
    getReward(e);
    uint256 rewardsAfter = rewards(user);
    uint256 rewardsTokenAfter = rewardsToken.balanceOf(user);

    assert rewardsBefore > 0 => rewardsAfter == 0, "Rewards didnt change correctly";
    assert rewardsBefore > 0 => rewardsTokenBefore < rewardsTokenAfter, "Rewards token didnt transfer correctly";

}

//Withdraw fails if the transfer failed
rule withdrawShouldFail(env e,address user, uint256 amount) {
    firstSetup(e,user);
    require stakingToken.balanceOf(currentContract) < amount;
    withdraw@withrevert(e,amount);

    assert lastReverted, "Withdraw should fail if the transfer fails(transfering more staking tokens than the balanceOf(address(this)))";
}

//Stake fails when transferFrom fails
rule stakeShouldFail(env e,address user, uint256 amount) {
    firstSetup(e,user);
    require stakingToken.balanceOf(user) < amount;
    stake@withrevert(e,amount);

    assert lastReverted, "Staking should fail if the transferFrom fails(transfering more staking tokens than the balanceOf(user))";
}

//getReward should fail the transfer of the token fails
rule getRewardShouldFail(env e,address user) {
    firstSetup(e,user);
    uint256 rewardsOfUser = rewards(user);
    require rewardsToken.balanceOf(currentContract) < rewardsOfUser;

    getReward@withrevert(e);

    assert lastReverted, "getRewards should fail if the transfer fails(transfering more reward tokens than the balanceOf(user))";
}


/**************************************************
 *              Risk Assessement                   *
 **************************************************/
//User can't withdraw all the funds twice
rule userCantWithdrawTwice(env e,method f, address user) {
    require e.msg.sender == user;
    uint256 amount = balanceOf(user);
    withdraw(e,amount);
    uint256 amount2;
    withdraw@withrevert(e,amount2);
    
    assert lastReverted, "User withdraw twice";
}

//Function with onlyOwner should revert if the caller is not the owner()
rule revertIfNotOwner(env e) {
    address owner = owner();
    uint256 rewardRate = rewardRate();
    uint256 duration = duration();
    uint256 time;
    uint256 amount;
    require e.msg.value == 0;
    require finishAt() < e.block.timestamp;
    require rewardRate > 0 && rewardRate * duration <= rewardsToken.balanceOf(currentContract);
    setRewardsDuration@withrevert(e,time);
    bool setRewardReverted = lastReverted;
    notifyRewardAmount@withrevert(e,amount);
    bool notifyRewardReverted = lastReverted;

    assert (setRewardReverted && notifyRewardReverted) <=> e.msg.sender != owner , "Functions didn't revert when caller was not the owner";
}

//User can't withdraw more then staked
rule cannotWithdrawMoreThanStaked(env e, address user, uint256 amount) {
    firstSetup(e,user);
    uint256 amountDeposited = balanceOf(user);
    withdraw@withrevert(e,amount);

    assert amount > amountDeposited => lastReverted;
}

//Any action should change only one user balance
rule anyActionChangeBalance(env e, method f, address user1,address user2){
    uint256 user1Balance = balanceOf(user1);
    uint256 user2Balance = balanceOf(user2);
    calldataarg args;
    f(e,args);

    assert (user1Balance != balanceOf(user1) && user2Balance != balanceOf(user2)) => user1 == user2, "An action changed the balance of multiple users";
}

//Any action should have effect only on one user assets
rule anyActionChangeAssets(env e, method f, address user1, address user2){
    require user1 != user2;
    calldataarg args;

    uint256 user1Balance = balanceOf(user1);
    uint256 user2Balance = balanceOf(user2);

    uint256 user1StakingBalance = stakingToken.balanceOf(user1);
    uint256 user2StakingBalance = stakingToken.balanceOf(user2);

    uint256 user1RewardToken = rewardsToken.balanceOf(user1);
    uint256 user2RewardToken = rewardsToken.balanceOf(user2);
    
    f(e,args);

    assert ((user1Balance != balanceOf(user1) || user1StakingBalance != stakingToken.balanceOf(user1) || user1RewardToken != rewardsToken.balanceOf(user1)) &&
    (user2Balance != balanceOf(user2) || user2StakingBalance != stakingToken.balanceOf(user2) || user2RewardToken != rewardsToken.balanceOf(user2))) => (((user1 == e.msg.sender && user2 == currentContract) ||
    user2 == e.msg.sender && user1 == currentContract) || (f.selector == rewardTransferTest(address,uint256).selector)), "An action changed the assets of multiple users";
}

