contract C13 {
  bool b

  constructor () {
    b = False;
    skip
  }

  function pay(amount) {
    require (amount <= balance && not b);
    msg.sender ! amount
  }

  function lock() {
    require(msg.sender == 0);
    b = true
  }

}

/*
// not liquid
property {
    Forall xa
    [
      true
        ->
      Exists tx [1, xa]
      [
        ((app_tx_st.balance[xa] == st.balance[xa]  + st.balance))
      ]
    ]
}
*/

// liquid 
property {
    Forall xa
    [
      st.b == false
        ->
      Exists tx [1, xa]
      [
        ((app_tx_st.balance[xa] == st.balance[xa]  + st.balance))
      ]
    ]
}