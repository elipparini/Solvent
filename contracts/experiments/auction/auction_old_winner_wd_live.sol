contract Auction {
    const int deadline
    const int min_bid
    const address seller

    address winner
    int current_bid // current maximum bit
    bool closed     // becomes true when the auction is closed

    constructor(address b, int d, int m) { // FIXME: if parameter a is used instead of b -> NameError: name 'constructor_a' is not defined
        // require(b!=0 && m>0 && d>0);
        seller = b;
        deadline = d;
        min_bid = m;
        closed = false
    }
     
    function bid() payable {
        require(not closed);
        require (msg.value >= min_bid);
        // the current bid is greater than the previous ones 
        // this guarantees that the contract balance is strictly positive 
        require (msg.value > current_bid);
     
        // the previous maximum bid is returned to the previous winner
        winner!current_bid;
        
        // the new winner is set to the current (highest) bidder
        winner = msg.sender;
        current_bid = msg.value
    }    
    
    function close() {
        require (not closed);
        require (msg.sender == seller);
        require (block.number > deadline);
        closed = true;
        seller!balance
    }
}

// the seller can withdraw the current bid after the deadline
property  old_winner_wd_live {
    Forall xa
    [
      st.winner!=0 && not closed
        ->
      Exists tx [1, xa]
      [
        (app_tx_st.balance[st.winner] == st.balance[st.winner] + st.current_bid)
      ]
    ]
}

// the seller can withdraw the bid after the deadline