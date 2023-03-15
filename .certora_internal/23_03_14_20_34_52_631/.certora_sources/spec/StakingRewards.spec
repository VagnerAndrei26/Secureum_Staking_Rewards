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


/**************************************************
 *              High-level                        *
 **************************************************/

//Staking tokens shouldn't decrease the rewards
rule moreTokensStakedMoreRewards(env e1, address user) {
    uint256 amount;
    require user != currentContract;
    require e1.msg.sender == user;
    require totalSupply() != 0;
    uint256 userRewardPerTokenBefore = userRewardPerTokenPaid(user);
    uint256 amountEarnedBefore = rewards(user);
    stake(e1, amount);
    uint256 amountEarnedAfter = rewards(user);
    uint256 userRewardPerTokenAfter = userRewardPerTokenPaid(user);

 
    assert (amountEarnedBefore < amountEarnedAfter && userRewardPerTokenBefore < userRewardPerTokenAfter), "Less rewards after the user staked tokens";
}

//if you staked more time you get more rewards
rule moreTokensMoreTimeStaked(address user) {
   method f;
   require totalSupply() != 0;
   require rewardRate() !=0;

   //first stake
   uint amount;
   env e1;
   require e1.msg.sender == user;
   uint256 rewardsAmountBeforeFirstStake = rewards(user);
   stake(e1,amount);

   //second stake
   uint256 amount2;
   env e2;
   require e2.msg.sender == user;
   require e2.block.timestamp > e1.block.timestamp + 100;
   uint256 rewardsAmountBeforeSecondStake = rewards(user);
   stake(e1,amount2);


   //Withdraw
   env e3;
   require e3.block.timestamp > e2.block.timestamp + 100;
   require e3.msg.sender == user;
   withdraw(e3,amount + amount2);
   uint256 rewardsAmountAfterWithdraw = rewards(user);

    assert rewardsAmountBeforeFirstStake < rewardsAmountAfterWithdraw, "It was called later";
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
    
    assert lastReverted;
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