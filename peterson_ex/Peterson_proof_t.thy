theory Peterson_proof_t
  imports
    Peterson_tactic
begin
  
definition
  Peterson_mutex_prop_prog_t
where
  "Peterson_mutex_prop_prog_t \<equiv>
  (mutex_init,,
  (COBEGIN
    \<lbrace>True\<rbrace>
    WHILE True INV \<lbrace>True\<rbrace>
    DO
      \<lbrace>True\<rbrace> \<langle>\<acute>in1 := True,, \<acute>pr1 := 1\<rangle>;;
      \<lbrace>True\<rbrace> \<langle>\<acute>hold := 1,, \<acute>pr1 := 2\<rangle>;;
      \<lbrace>True\<rbrace>
      AWAIT (\<not>\<acute>in2 \<or> \<acute>hold \<noteq> 1) THEN \<acute>pr1 := 3 END;;
      \<lbrace>True\<rbrace>
      \<langle>\<acute>in1 := False,, \<acute>pr1 := 0\<rangle>
    OD
    \<lbrace>True\<rbrace>

    \<parallel>

    \<lbrace>True\<rbrace>
    WHILE True INV \<lbrace>True\<rbrace>
    DO
      \<lbrace>True\<rbrace> \<langle>\<acute>in2 := True,, \<acute>pr2 := 1\<rangle>;;
      \<lbrace>True\<rbrace> \<langle>\<acute>hold := 2,, \<acute>pr2 := 2\<rangle>;;
      \<lbrace>True\<rbrace>
      AWAIT (\<not>\<acute>in1 \<or> \<acute>hold \<noteq> 2) THEN \<acute>pr2 := 3 END;;
      \<lbrace>True\<rbrace>
      \<langle>\<acute>in2 := False,, \<acute>pr2 := 0\<rangle>
    OD 
    \<lbrace>True\<rbrace>
  COEND))"
  
lemmas Peterson_mutex_prop_prog_t_defs =
                Peterson_mutex_base_defs
                Peterson_mutex_prop_prog_t_def
  
  
  
  
end
  