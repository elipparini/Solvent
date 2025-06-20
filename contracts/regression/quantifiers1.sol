contract Quantifiers {

  function pippo (int n) payable {
        if (n=3) {  
            sender.transfer(1)
        }   else {
            skip
        }
  }
}

// Forall a. Exists n.
property liq1_liquid {
    Forall xa
    [
      st.balance>0
      ->
      Exists tx [1, xa]
      [
        ((<tx>balance[xa] = balance[xa]+1))
      ]
    ]
}


// Forall a. Forall n.
property liq2_notliquid {
    Forall xa
    [
      st.balance>0
      ->
      Forall n. Exists tx [1, xa]
      [
        ((<tx>balance[xa] = balance[xa]+1))
      ]
    ]
}


// Exists a. Exists n.
property liq3_liquid {
    Exists xa
    [
      st.balance>0
      ->
      Exists tx [1, xa]
      [
        ((<tx>balance[xa] = balance[xa]+1))
      ]
    ]
}


// Exists a. Forall n.
property liq4_notliquid {
    Exists xa
    [
      st.balance>0
      ->
      Forall n. Exists tx [1, xa]
      [
        ((<tx>balance[xa] = balance[xa]+1))
      ]
    ]
}