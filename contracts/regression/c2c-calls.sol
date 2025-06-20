contract C {

  function f() {
    D.g();
    sender.transfer(1)
  }
}

contract D {

  function g() {
    // require (msg.sender == C)
    sender.transfer(1)
  }
}




// (WEAK SAT - WEAK UNSAT)
// Can_Transactions_Arrive_Any_time=True: STRONG SAT
// not liquid
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

// STRONG UNSAT
// liquid
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