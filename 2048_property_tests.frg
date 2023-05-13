#lang forge "final" "nvliavoez7ahtpvr"

open "2048.frg"
open "2048.test.frg"

test expect {
  tracesSAT: { traces[4] } for optimizer4
    is sat




  
}


