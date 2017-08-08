theory Peterson_base
  imports
    "../verif/OG_More"
    Peterson_state
    "../lib/Hoare_Parallel/OG_Syntax"
    "../lib/subgoal_focus/Subgoal_Methods"
    "../lib/Eisbach_Methods"
begin
  
lemma CollectNotD: "a \<notin> {x. P x} \<Longrightarrow> \<not> P a"
  by simp

lemmas Collect_conj_eq_rev = Collect_conj_eq[symmetric]
lemmas subset_eqI = subset_eq[THEN iffD2]

lemma
  union_negI: 
  "(x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> x \<in> A \<union> -B"
  by blast

lemma
  union_negI_drop: 
  "x \<in> A \<Longrightarrow> x \<in> A \<union> -B"
  by blast

lemma
  last_single: 
  "last [x] = x"
  by simp

lemmas svc\<^sub>a_commute = eq_commute[where a=svc\<^sub>a]
lemmas svc\<^sub>s_commute = eq_commute[where a=svc\<^sub>s]
  
  
  
  
  
definition
  mutex_init
where
  "mutex_init \<equiv>  
    \<acute>pr1 := 0,,
    \<acute>in1 := False,,
    \<acute>pr2 := 0,,
    \<acute>in2 := False"
  
lemmas Peterson_mutex_base_defs =
  mutex_init_def
  
end
  