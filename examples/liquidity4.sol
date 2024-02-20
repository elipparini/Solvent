contract C4 {

  constructor () {
    skip
  }

  function pay(amount) {
    require (amount<=(balance - 1));
    sender!amount
  }
}


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


/*
// liquid
property {
    Forall xa
    [
      st.balance > 1
        ->
      Exists tx [1, xa]
      [
        ((app_tx_st.balance[xa] == st.balance[xa]  + (st.balance - 1)))
      ]
    ]
}
*/