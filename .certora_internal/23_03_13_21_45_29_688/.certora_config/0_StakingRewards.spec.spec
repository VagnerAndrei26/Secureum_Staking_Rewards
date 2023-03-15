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


rule sanity(env e, method f){
    calldataarg args;
    f(e,args);
    assert false;
}

rule onlyTheOwnerCanChangeTheDuration(env e, uint time){
    uint256 _duration = duration();
    require time != _duration;
    setRewardsDuration(e, time);
    uint256 duration_ = duration();
    assert _duration != duration_ <=> e.msg.sender == owner(), "Only the owner can change the time";
}

rule revertIfNotOwner(env e) {
    // require e.msg.sender != owner();
    uint256 time;
    setRewardsDuration@withrevert(e,time);
    bool setRewardReverted = lastReverted;
    uint amount;
    notifyRewardAmount@withrevert(e,amount);
    bool notifyRewardReverted = lastReverted;

    assert (setRewardReverted && notifyRewardReverted) , "Functions didn't revert when caller was not the owner";
}