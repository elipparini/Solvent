contract Rich {
  bool lock;

  constructor () {
    lock = true
  }

  function unlock() payable {
    //require(lock && msg.value == 1000); 
    require(lock && msg.value == 2000); 
    lock = false
  }

  function pay(int amount) {
    require (!lock);
    msg.sender.transfer(amount)
  }

}

property wd1_nonliquid {
    Forall xa
    [
      st.balance >= 1 && lock 
        ->
      Exists tx [1, xa]
      [
        ((<tx>balance[xa] >= balance[xa]  + 1))
      ]
    ]
}


property unlock_nonliquid {
    Forall xa
    [
      balance >= 1 && lock && balance[xa]>=1000
        ->
      Exists tx [1, xa]
      [
        ((<tx>lock == false))
      ]
    ]
}


property unlock_liquid {
    Forall xa
    [
      balance >= 1 && lock && balance[xa]>=2000
        ->
      Exists tx [1, xa]
      [
        ((<tx>lock == false))
      ]
    ]
}

/*


property wd2_1tx_nonliquid {
    Forall xa
    [
      balance >= 1 && lock && balance[xa]>=1000
        ->
      Exists tx [1, xa]
      [
        ((<tx>balance[xa] >= balance[xa]  + 1))
      ]
    ]
}

property wd2_2tx_nonliquid {
    Forall xa
    [
      balance >= 1 && lock && balance[xa]>=1000
        ->
      Exists tx [2, xa]
      [
        ((<tx>balance[xa] >= balance[xa]  + 1))
      ]
    ]
}
*/