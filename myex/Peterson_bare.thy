theory Peterson_bare
  imports 
    Main
     "../verif/OG_Bare"
begin
  
record Peterson_mutex =
  pr1 :: nat
  pr2 :: nat
  in1 :: bool
  in2 :: bool
  hold :: nat
  
  
end
  