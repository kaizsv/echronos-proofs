theory Peterson_base
  imports
    "../verif/OG_More"
    Peterson_state
    "../lib/Hoare_Parallel/OG_Syntax"
    "../lib/subgoal_focus/Subgoal_Methods"
    "../lib/Eisbach_Methods"
begin
  
lemma helper':
    "  Some n = s \<Longrightarrow>
       Some(the s) = s "
  by auto
    
lemma helper6:
  " \<lbrakk> Some n = a; n \<notin> I \<rbrakk> \<Longrightarrow> the a \<notin> I"
  by auto

lemma helper7:
  "\<lbrakk> A - B = {u}; x \<in> A; x \<notin> B\<rbrakk> \<Longrightarrow> x = u"
  by auto

lemma helper8:
  "card A \<le> Suc 0 \<Longrightarrow> A = {} \<or> (\<exists>u. A = {u}) \<or> \<not> finite A"
  by (auto simp: le_eq_less_or_eq dest: card_eq_SucD)
    
lemma helper13:
  "x \<in> (if b then c else {}) \<Longrightarrow> b"
  by (case_tac b, auto)
    
lemma helper15:
  "x \<in> set xs \<Longrightarrow> xs \<noteq> []"
  by auto
    
lemma helper16:
  "\<lbrakk>distinct xs; tl xs \<noteq> []\<rbrakk> \<Longrightarrow> last xs \<noteq> hd xs"
  by (cases xs) auto
    
lemma helper17:
  "\<lbrakk>distinct xs; xs \<noteq> []; last xs = hd xs\<rbrakk> \<Longrightarrow> tl xs = []"
  apply (clarsimp simp: last_conv_nth hd_conv_nth nth_eq_iff_index_eq)
  apply (cases xs, simp+)
  done

lemma helper18:
  "distinct xs \<Longrightarrow> hd xs \<notin> set (tl xs)"
  by (cases xs) auto

lemma helper19[simp]:
  "x \<notin> set xs \<Longrightarrow> x \<notin> set (tl xs)"
  by (cases xs) auto
    
lemma helper21:
  "x \<in> set xs \<Longrightarrow> x = hd xs \<or> x \<in> set (tl xs)"
  by (cases xs) auto

lemma helper21':
  "hd xs \<noteq> x \<Longrightarrow> x \<notin> set (tl xs) \<Longrightarrow> x \<notin> set xs"
  by (cases xs) auto

lemma helper22:
  "xs \<noteq> [] \<Longrightarrow> x \<notin> set xs \<Longrightarrow> x \<noteq> hd xs \<and> x \<notin> set (tl xs)"
  by (cases xs) auto

lemma helper23:
  "\<lbrakk>x \<in> A; x \<in> set xs; last xs \<notin> A \<rbrakk> \<Longrightarrow> tl xs \<noteq> []"
  by (cases xs) auto

lemma helper23':
  "\<lbrakk>x \<notin> A; x \<in> set xs; last xs \<in> A \<rbrakk> \<Longrightarrow> tl xs \<noteq> []"
  by (cases xs) auto
    
lemma helper26:
  "y \<in> set xs \<Longrightarrow> last xs \<in> U \<Longrightarrow> y \<notin> U \<Longrightarrow> last xs = x
    \<Longrightarrow> last (tl xs) = x"
  by (auto simp: List.last_tl helper23')

lemma helper27:
  "x = y \<or> P \<Longrightarrow> x \<in> I \<Longrightarrow> y \<notin> I \<Longrightarrow> P"
  by auto
    
lemma helper28:
  "x = y \<or> P \<Longrightarrow> x \<in> U \<Longrightarrow> y \<notin> U \<Longrightarrow> P"
  by auto

lemma helper30:
  "P \<or> P' \<Longrightarrow> P \<longrightarrow> Q \<Longrightarrow> P' \<longrightarrow> Q \<Longrightarrow> Q"
  by auto

lemma last_in_set_tl:
  "last as \<noteq> hd as \<Longrightarrow> last as \<in> set (tl as)"
  apply (cases as)
   apply (simp add: last_def hd_def)
  apply clarsimp
  done
    
lemma last_tl_hd:
  "last as \<noteq> hd as \<Longrightarrow> last (tl as) = last as"
  by (cases as) auto

lemmas last_tl' = last_tl[symmetric, THEN subst, rotated]

lemmas set_tl = list.set_sel(2)[rotated]
  
(*** many sorted by * policy ***)
(************* SKIP ************)
  
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
    
(* implied invariants *)
  
  
  
  
  
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
  