contract C4 {
  int a; 
  int b; 
  int c; 
  constructor () {
    a = 0;
    b = 0;
    c = 0;
    skip
  }

  function pay(int amount) {
    require (a == b);
    payable(sender).transfer(amount);
    a = a+1;
    b = b+1
  }
}

property liquidity1_liquid {
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


property safety_true {
    Forall xa
    [
      true
        ->
      Exists tx [1, xa]
      [
        (a == b)
      ]
    ]
}


property safety_false {
    Forall xa
    [
      true
        ->
      Exists tx [1, xa]
      [
        (a == c)
      ]
    ]
}