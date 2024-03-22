contract C12 {

  constructor () {
    skip
  }

  function pay(amount) {
    require (amount <= balance);
    if (msg.sender != 0) {
      msg.sender ! amount - 1
    }
    else {
      msg.sender ! amount
    }
  }

}

// STRONG SAT
// (Can_Transactions_Arrive_Any_time=False WEAK SAT WEAK UNSAT)
// not liquid
property liquidity12a_nonliq {
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


// STRONG SAT
// (Can_Transactions_Arrive_Any_time=False WEAK SAT WEAK UNSAT)
// not  liquid
property liquidity12b_nonliq {
    Forall xa
    [
      xa != 0
        ->
      Exists tx [1, xa]
      [
        ((app_tx_st.balance[xa] == st.balance[xa]  + st.balance ))
      ]
    ]
}