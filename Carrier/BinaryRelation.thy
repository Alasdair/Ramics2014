theory BinaryRelation
  imports KAT
begin

(* (UNIV, \<subseteq> ) is a Boolean Algebra *)
abbreviation BA where  "BA \<equiv>  \<lparr> carrier = UNIV, le = op \<subseteq>  \<rparr>"

lemma ba_order: "order BA"
  by default auto

lemma ba_join_semilattice: "join_semilattice BA"
  by (auto simp add: join_semilattice_def join_semilattice_axioms_def ba_order order.is_lub_simp[OF ba_order])

lemma ba_meet_semilattice: "meet_semilattice BA"
  by (auto simp add: meet_semilattice_def meet_semilattice_axioms_def ba_order order.is_glb_simp[OF ba_order])

lemma ba_lattice: "lattice BA"
  by (simp add: lattice_def ba_join_semilattice ba_meet_semilattice)

lemma ba_join: "x \<squnion>\<^bsub>BA\<^esub> y = x \<union> y"
  apply (simp add: order.join_def[OF ba_order] order.lub_simp[OF ba_order])
  by (rule the1I2, rule ex_ex1I, blast, metis equalityI, blast) 

lemma ba_meet: "x \<sqinter>\<^bsub>BA\<^esub> y = x \<inter> y"
  apply (simp add: order.meet_def[OF ba_order] order.glb_simp[OF ba_order])
  by (rule the1I2, rule ex_ex1I, blast, metis equalityI, blast)

lemma ba_distr_lattice: "distributive_lattice BA"
  by (auto simp add: distributive_lattice_def distributive_lattice_axioms_def ba_lattice ba_join ba_meet)

lemma ba_bounded_lattice: "bounded_lattice BA"
 by (auto simp add: bounded_lattice_def bounded_lattice_axioms_def ba_lattice ba_join ba_meet)

lemma ba_comp_lattice: "complemented_lattice BA"
  apply (simp add: complemented_lattice_def complemented_lattice_axioms_def ba_bounded_lattice ba_join ba_meet bounded_lattice.top_def[OF ba_bounded_lattice] bounded_lattice.bot_def[OF ba_bounded_lattice])
  by ((rule the1I2, blast)+, metis Diff_disjoint Un_Diff_cancel subset_empty sup_absorb2)

lemma ba_boolean_algebra: "boolean_algebra BA"
  by (simp add: boolean_algebra_def ba_distr_lattice ba_comp_lattice)

interpretation rel_ba: boolean_algebra "BA"
  by (simp add: ba_boolean_algebra)

(* Tests, (R \<subseteq> Id, \<subseteq> ), is a Boolean Algebra *)
abbreviation TestBA where "TestBA \<equiv> \<lparr> carrier = {R. R \<subseteq>  Id}, le = op \<subseteq>  \<rparr>"

lemma test_order [intro!]: "order TestBA"
  by default auto

lemma test_join_semilattice: "join_semilattice TestBA"
  by (auto simp add: join_semilattice_def join_semilattice_axioms_def order.is_lub_simp[OF test_order])

lemma test_meet_semilattice: "meet_semilattice TestBA"
  apply (simp add: meet_semilattice_def meet_semilattice_axioms_def test_order, auto)
  by (simp add:  order.is_glb_simp[OF test_order], rule_tac x = "x \<inter> y" in exI, auto)

lemma test_lattice[intro!]: "lattice TestBA"
  by (simp add: lattice_def, metis test_join_semilattice test_meet_semilattice)

lemma test_join: "\<lbrakk>x \<subseteq> Id; y \<subseteq> Id\<rbrakk> \<Longrightarrow> x \<squnion>\<^bsub>TestBA\<^esub> y = x \<union> y"
  apply (simp add: order.join_def[OF test_order] order.lub_simp[OF test_order])
  by (rule the1I2, rule ex_ex1I, blast, metis equalityI, default, auto)

lemma test_meet: "\<lbrakk>x \<subseteq> Id; y \<subseteq> Id\<rbrakk> \<Longrightarrow> x \<sqinter>\<^bsub>TestBA\<^esub> y = x \<inter> y"
  apply (simp add: order.meet_def[OF test_order] order.glb_simp[OF test_order])
  apply (rule the1I2, rule ex_ex1I, rule_tac x = "x \<inter> y" in exI, blast, metis equalityI)
  by (metis (no_types) inf_sup_aci(1) inf_sup_aci(2) inf_sup_ord(2) le_iff_inf le_inf_iff)

lemma test_union_closure: "\<lbrakk>x \<subseteq> Id; y \<subseteq> Id\<rbrakk> \<Longrightarrow> x \<union> y \<subseteq> Id"
  by auto

lemma test_inter_closure: "\<lbrakk>x \<subseteq> Id; y \<subseteq> Id\<rbrakk> \<Longrightarrow> x \<inter> y \<subseteq> Id"
  by auto

lemma test_distr_lattice: "distributive_lattice TestBA"
  by (auto simp add: distributive_lattice_def distributive_lattice_axioms_def test_lattice test_inter_closure test_join test_meet)

lemma test_bounded_lattice: "bounded_lattice TestBA"
 by (auto simp add: bounded_lattice_def bounded_lattice_axioms_def test_lattice test_join test_meet)

lemma test_top: "bounded_lattice.top TestBA = Id"
  by (simp add: bounded_lattice.top_def[OF test_bounded_lattice], rule theI2, blast+)

lemma test_bot: "bounded_lattice.bot TestBA = {}"
  by (simp add: bounded_lattice.bot_def[OF test_bounded_lattice], rule theI2, blast+)

lemma test_comp_lattice: "complemented_lattice TestBA"
  apply (simp add: complemented_lattice_def complemented_lattice_axioms_def test_bounded_lattice test_top test_bot) 
  apply default
  apply (rule impI)
  apply (rule_tac x = "(- x) \<inter> Id" in exI)
  by (auto simp add: test_meet test_join)

lemma test_boolean_algebra: "boolean_algebra TestBA"
  by (simp add: boolean_algebra_def test_distr_lattice test_comp_lattice)

interpretation rel_test: boolean_algebra "TestBA"
  by (simp add: test_boolean_algebra)

(* KAT *)
abbreviation RelKAT where "RelKAT \<equiv> \<lparr> carrier = UNIV
  , plus = op \<union>
  , mult = op O
  , one = Id
  , zero = {}
  , star = rtrancl
  , test = TestBA
\<rparr>"

lemma kat_dioid: "dioid RelKAT"
  by default auto

lemma kat_nat_order: "(dioid.nat_order RelKAT x y) \<longleftrightarrow> (x \<subseteq> y)"
  apply (simp add: dioid.nat_order_def[OF kat_dioid])
  by (metis subset_Un_eq)

lemma power_is_relpow: "rtrancl X = (\<Union>n. X ^^ n)"
by (metis rtrancl_is_UN_relpow)

lemma rel_star_contl: "X O Y^* = (\<Union>n. X O Y ^^ n)"
by (metis power_is_relpow relcomp_UNION_distrib)

lemma rel_star_contr: "X^* O Y = (\<Union>n. X ^^ n O Y)"
by (metis power_is_relpow relcomp_UNION_distrib2)

lemma power_inductl: "z \<subseteq> y \<and> x O y \<subseteq> y \<longrightarrow> x^^n O z \<subseteq> y"
  apply ((induct n), force)
  by (smt O_assoc atMost_subset_iff order_subst2 relcomp_distrib relpow.simps(2) relpow_commute subset_Un_eq)

lemma power_inductr: "z \<subseteq> y \<and> y O x \<subseteq> y \<longrightarrow> z O x^^n \<subseteq> y"
  by (induct n) auto

lemma kat_kleene_algebra: "kleene_algebra RelKAT"
  apply (simp add: kleene_algebra_def kleene_algebra_axioms_def kat_dioid)
  apply (intro conjI allI)
  apply (simp_all add: kat_nat_order)
  apply (metis Un_upper1 Un_upper2 r_comp_rtrancl_eq rtrancl_unfold)
  apply (metis Un_upper1 Un_upper2 rtrancl_unfold)
  apply (simp add: rel_star_contr)
  apply (metis (mono_tags) SUP_le_iff power_inductl)
  apply (simp add: rel_star_contl)
  by (metis (mono_tags) SUP_le_iff power_inductr)
 
lemma kat_kat': "kat' RelKAT"
  apply (simp add: kat'_def kat_kleene_algebra test_boolean_algebra)
  by ((rule ext)+, metis kat_nat_order)

lemma kat_kat: "kat RelKAT"
  by (simp add: kat_def kat_axioms_def kat_kleene_algebra kat_kat' test_top test_bot test_meet test_join, blast)

interpretation rel_kat2: kat "RelKAT"
  by (simp add: kat_kat)
                                         
hide_const BA
hide_const TestBA
hide_const RelKAT

end