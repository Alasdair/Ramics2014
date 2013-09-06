theory KAT
  imports Kleene_Algebra_Left Tests
begin

class kat_zerol = kleene_algebra_zerol + dioid_tests
begin

lemma star_sim_right: "\<lbrakk>test b; b\<cdot>q = q\<cdot>b\<rbrakk> \<Longrightarrow> b\<cdot>q\<^sup>\<star> = (b\<cdot>q)\<^sup>\<star>\<cdot>b"
proof - 
  assume tb: "test b" and comm: "b\<cdot>q = q\<cdot>b"
  hence comm2: "b\<cdot>q = b\<cdot>q\<cdot>b"
    by (metis mult_assoc test_mult_idem_var)
  moreover hence "b + (b\<cdot>q)\<^sup>\<star>\<cdot>b\<cdot>q = (1 + (b\<cdot>q)\<^sup>\<star>\<cdot>b\<cdot>q)\<cdot>b"
    by (metis distrib_right' mult_assoc mult_onel)
  moreover hence "... = (b\<cdot>q)\<^sup>\<star>\<cdot>b"
    by (metis star_prod_unfold star_slide)
  ultimately have "b\<cdot>q\<^sup>\<star> \<le> (b\<cdot>q)\<^sup>\<star>\<cdot>b"
    by (metis order_refl star_sim2)
  thus ?thesis
    by (metis comm2 eq_iff star_sim1)
qed

lemma star_sim_left: "\<lbrakk>test b; b\<cdot>q = q\<cdot>b\<rbrakk> \<Longrightarrow> b\<cdot>q\<^sup>\<star> = b\<cdot>(q\<cdot>b)\<^sup>\<star>"
  by (metis star_sim_right star_slide)

lemma comm_star: "\<lbrakk>test b; b\<cdot>p = p\<cdot>b; b\<cdot>q = q\<cdot>b\<rbrakk> \<Longrightarrow> b\<cdot>p\<cdot>(b\<cdot>q)\<^sup>\<star> = b\<cdot>p\<cdot>q\<^sup>\<star>"
  by (metis star_sim_right mult_assoc star_slide)

end

text {*
  Kleene Algebra with Tests is defined with an embedded Boolean Algebra.
*}

class kat = kleene_algebra + dioid_tests
begin

subclass kat_zerol
  apply (unfold_locales)
  by (metis star_inductr)

lemma kat_eq1: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p\<cdot>x\<cdot>!q = 0) = (p\<cdot>x = p\<cdot>x\<cdot>q)"
  apply default
  apply (subgoal_tac "p \<cdot> x = p \<cdot> x \<cdot> (q + ! q)")
  apply (metis add_0_left add_commute distrib_left)
  apply (metis mult_1_right test_add_comp test_def)
  by (metis annir test_double_comp_var test_mult_comp mult_assoc)

lemma kat_eq2: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p\<cdot>x\<cdot>!q = 0) = (p\<cdot>x \<le> x\<cdot>q)"
  apply default
  apply (metis add_idem' kat_eq1 less_eq_def mult_1_left mult_assoc star_inductl_var_equiv star_subid test_ub_var)
  apply (subgoal_tac "p \<cdot> x \<cdot> ! q \<le> x \<cdot> q \<cdot> ! q")
  apply (metis annir test_double_comp_var test_mult_comp mult_assoc zero_unique)
  by (metis mult_isor)

text {* 
  Some commutativity conditions equivalence lemmas 
*}
lemma comm_eq1: "test b \<Longrightarrow> (p\<cdot>b = b\<cdot>p) = (b\<cdot>p\<cdot>!b + !b\<cdot>p\<cdot>b = 0)"
  apply default
  apply (metis add_0_left annil annir test_double_comp_var test_mult_comp mult_assoc)
  by (metis add_0_left ba6 de_morgan1 distrib_right' test_double_comp_var kat_eq1 test_one mult_assoc mult_onel no_trivial_inverse test_comp_closed_var test_not_one)

lemma comm_eq2: "test b \<Longrightarrow> (p\<cdot>!b = !b\<cdot>p) = (b\<cdot>p\<cdot>!b + !b\<cdot>p\<cdot>b = 0)"
  by (metis add_comm comm_eq1 test_comp_closed_var test_double_comp_var)

lemma comm_eq3: "test b \<Longrightarrow> (p\<cdot>b = b\<cdot>p) = (p\<cdot>!b = !b\<cdot>p)"
  by (metis comm_eq1 comm_eq2)

end

end
