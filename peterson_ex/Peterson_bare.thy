theory Peterson_bare
  imports
    Peterson_state
    "../verif/OG_Bare"
begin
  
definition
  mutex_init :: "('a Peterson_state_ext) bare_com"
where
  "mutex_init \<equiv>  
    \<acute>pr1 := 0;;
    \<acute>in1 := False;;
    \<acute>pr2 := 0;;
    \<acute>in2 := False"
  
definition
  Peterson_mutex :: "('a Peterson_state_ext) bare_com"
  where
    "Peterson_mutex \<equiv>
      mutex_init;;
     (COBEGIN
      WHILE True
      DO
      \<langle>\<acute>in1 := True,, \<acute>pr1 := 1\<rangle>;;
      \<langle>\<acute>hold := 1,, \<acute>pr1 := 2\<rangle>;;
      AWAIT (\<not>\<acute>in2 \<or> \<not>(\<acute>hold=1)) THEN \<acute>pr1 := 3 END;;
      \<langle>\<acute>in1 := False,, \<acute>pr1 := 0\<rangle>
      OD
      \<parallel>
      WHILE True
      DO
      \<langle>\<acute>in2 := True,, \<acute>pr2 := 1\<rangle>;;
      \<langle>\<acute>hold := 2,, \<acute>pr2 := 2\<rangle>;;
      AWAIT (\<not>\<acute>in1 \<or> \<not>(\<acute>hold=2)) THEN \<acute>pr2 := 3 END;;
      \<langle>\<acute>in2 := False,, \<acute>pr2 := 0\<rangle>
      OD
      COEND)"
    
lemmas Peterson_mutex_defs =
  Peterson_mutex_def
thm Peterson_mutex_def[simplified Peterson_mutex_defs]
    
end
  