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
invariant sumOfBalancesIsEQToTotalSupply(env e)
    totalSupply() == sumOfBalances


rule sanity(env e, method f){
    calldataarg args;
    f(e,args);
    assert false;
}

rule revertIfNotOwner(env e) {
    require e.msg.sender != owner();
    uint256 time;
    setRewardsDuration@withrevert(e,time);
    bool setRewardReverted = lastReverted;
    uint amount;
    notifyRewardAmount@withrevert(e,amount);
    bool notifyRewardReverted = lastReverted;

    assert (setRewardReverted && notifyRewardReverted) , "Functions didn't revert when caller was not the owner";
}


//Variable Transition
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

//Risk assessement
//User can't withdraw all the funds twice

rule userCantWithdrawTwice(env e,method f, address user) {
    require e.msg.sender == user;
    uint256 amount = balanceOf(user);
    withdraw(e,amount);
    uint256 amount2;
    withdraw@withrevert(e,amount2);
    
    assert lastReverted;
}

//Valid state
//Total supply is greater than 0 only if balanceOf(user) is 0

invariant totalSupplyToBalanceOf(address user)
    totalSupply() == 0 <=> balanceOf(user) == 0