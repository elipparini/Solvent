contract C4 {
  
  constructor () {
    skip
  }

  function pay(int amount) {
    require (amount<=(balance - 1));
    payable(sender).transfer(amount)
  }
}

/*
property liquidity1_nonliquid {
    Forall xa
    [
      true
        ->
      Exists tx [1, xa]
      [
        ((<tx>balance[xa] == balance[xa]  + balance))
      ]
    ]
}
*/

property liquidity1_nonliquid {
  forall a : address .
  exists args : calldataargs . 
  exists v : int .   
    <a : C4.pay()$v>		
      balance(a) = old(balance(a)) + 1
}

/*
property liquidity2_liquid {
    Forall xa
    [
      st.balance > 1
        ->
      Exists tx [1, xa]
      [
        ((<tx>balance[xa] == st.balance[xa]  + (st.balance - 1)))
      ]
    ]
}
*/

property liquidity2_liquid {
  balance(C4) > 1 
    ->
  forall a : address .
  exists args : calldataargs . 
  exists v : int .   
    <a : C4.pay()$v>		
      balance(a) = old(balance(a)) + 1
}


property liquidity3_nonliquid {
  forall a : address .
  exists args : calldataargs . 
  exists v : int .   
    <a : C4.pay()$v>		
      !lastReverted
}


property liquidity4_liquid {
  balance(C4) > 1 
    ->
  forall a : address .
  exists args : calldataargs . 
  exists v : int .   
    <a : C4.pay()$v>		
      !lastReverted
}