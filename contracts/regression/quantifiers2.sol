contract Quantifiers {

  function pippo (int n) payable {
        if (n>3 || msg.value < 7) {  
            sender.transfer(balance)
        }   else {
            skip
        }
  }


  function pluto (int n, int m) payable {
        if (n>3 || msg.value < 7) {  
            sender.transfer(balance)
        }   else {
            skip
        }
  }
}

property liq1_liquid {
    Forall xa
    [
      st.balance>0
      ->
      Exists tx [1, xa]
      [
        ((<tx>balance[xa] = balance[xa] + balance))
      ]
    ]
}


// Forall a. Exists xn. Forall n.
property liq2_notliquid {
    Forall xa
    [
      st.balance>0
      ->
      Exists xn. Forall n. Exists tx [1, xa]
      [
        ((<tx>balance[xa] = balance[xa] + balance))
      ]
    ]
}

