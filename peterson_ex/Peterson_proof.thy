theory Peterson_proof
  imports
    Peterson_tactic
begin
  
definition
  Peterson_mutex_prop_prog
where
  "Peterson_mutex_prop_prog \<equiv>
  (mutex_init,,
  (COBEGIN
    \<lbrace>\<acute>pr1 = 0 \<and> \<not>\<acute>in1\<rbrace>
    WHILE True INV \<lbrace>\<acute>pr1 = 0 \<and> \<not>\<acute>in1\<rbrace>
    DO
      \<lbrace>\<acute>pr1 = 0 \<and> \<not>\<acute>in1\<rbrace> \<langle>\<acute>in1 := True,, \<acute>pr1 := 1\<rangle>;;
      \<lbrace>\<acute>pr1 = 1 \<and> \<acute>in1\<rbrace> \<langle>\<acute>hold := 1,, \<acute>pr1 := 2\<rangle>;;
      \<lbrace>\<acute>pr1 = 2 \<and> \<acute>in1 \<and> (\<acute>hold = 1 \<or> (\<acute>hold = 2 \<and> \<acute>pr2 = 2))\<rbrace>
      AWAIT (\<not>\<acute>in2 \<or> \<acute>hold \<noteq> 1) THEN \<acute>pr1 := 3 END;;
      \<lbrace>\<acute>pr1 = 3 \<and> \<acute>in1 \<and> (\<acute>hold = 1 \<or> (\<acute>hold = 2 \<and> \<acute>pr2 = 2))\<rbrace>
      \<langle>\<acute>in1 := False,, \<acute>pr1 := 0\<rangle>
    OD
    \<lbrace>\<acute>pr1 = 0 \<and> \<not>\<acute>in1\<rbrace>

    \<parallel>

    \<lbrace>\<acute>pr2 = 0 \<and> \<not>\<acute>in2\<rbrace>
    WHILE True INV \<lbrace>\<acute>pr2 = 0 \<and> \<not>\<acute>in2\<rbrace>
    DO
      \<lbrace>\<acute>pr2 = 0 \<and> \<not>\<acute>in2\<rbrace> \<langle>\<acute>in2 := True,, \<acute>pr2 := 1\<rangle>;;
      \<lbrace>\<acute>pr2 = 1 \<and> \<acute>in2\<rbrace> \<langle>\<acute>hold := 2,, \<acute>pr2 := 2\<rangle>;;
      \<lbrace>\<acute>pr2 = 2 \<and> \<acute>in2 \<and> (\<acute>hold = 2 \<or> (\<acute>hold = 1 \<and> \<acute>pr1 = 2))\<rbrace>
      AWAIT (\<not>\<acute>in1 \<or> \<acute>hold \<noteq> 2) THEN \<acute>pr2 := 3 END;;
      \<lbrace>\<acute>pr2=3 \<and> \<acute>in2 \<and> (\<acute>hold = 2 \<or> (\<acute>hold = 1 \<and> \<acute>pr1 = 2))\<rbrace>
      \<langle>\<acute>in2 := False,, \<acute>pr2 := 0\<rangle>
    OD 
    \<lbrace>\<acute>pr2 = 0 \<and> \<not>\<acute>in2\<rbrace>
  COEND))"
  
  
lemmas Peterson_mutex_prop_prog_defs =
                Peterson_mutex_base_defs
                Peterson_mutex_prop_prog_def
                
lemma Peterson_mutex_prop_proof:
  "\<lbrace>True\<rbrace>
   \<parallel>-\<^sub>i \<lbrace>mutex_invariante\<rbrace> \<lbrace>\<acute>mutex_precondition\<rbrace>
    Peterson_mutex_prop_prog
    \<lbrace>\<acute>mutex_postcondition\<rbrace>"
  unfolding Peterson_mutex_prop_prog_defs
  unfolding oghoare_inv_def
    sorry
  
  
  
  
end
  