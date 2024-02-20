contract C14 {
  bool b

  constructor () {
    b = False;
    skip
  }

  function unlock() {
    require(not b); 
    b = true
  }

  function pay(amount) {
    require (amount <= balance && b);
    b = False;
    sender ! amount
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
      st.b == true
        ->
      Exists tx [1, xa]
      [
        ((app_tx_st.balance[xa] == st.balance[xa]  + st.balance))
      ]
    ]
}


/*
//  liquid
property {
    Forall xa
    [
      true
        ->
      Exists tx [2, xa]
      [
        ((app_tx_st.balance[xa] == st.balance[xa]  + st.balance ))
      ]
    ]
}

//  liquid
property {
    Forall xa
    [
      st.b==true
        ->
      Exists tx [2, xa]
      [
        ((app_tx_st.balance[xa] == st.balance[xa]  + st.balance ))
      ]
    ]
}
*/