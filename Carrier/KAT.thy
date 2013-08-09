theory KAT
  imports Kleene_Algebra
begin

record 'a test_algebra = "'a kleene_algebra" +
  test :: "'a ord"

abbreviation tests :: "('a, 'b) test_algebra_scheme \<Rightarrow> 'a set" where
    "tests A \<equiv> carrier (test A)"

locale kat' =
  fixes A :: "('a, 'b) test_algebra_scheme" (structure)
  assumes kat_ka: "kleene_algebra A"
  and test_subset: "tests A \<subseteq> carrier A"
  and test_le [simp]: "le (test A) = dioid.nat_order A"
  and test_ba: "boolean_algebra (test A)"

sublocale kat' \<subseteq> kleene_algebra using kat_ka .

locale kat = kat' +
  assumes test_one: "bounded_lattice.top (test A) = 1"
  and test_zero: "bounded_lattice.bot (test A) = 0"
  and test_join: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> order.join (test A) x y = x + y"
  and test_meet: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> order.meet (test A) x y = x \<cdot> y"

sublocale kat \<subseteq> test: boolean_algebra "test A"
  where "bounded_lattice.top (test A) = 1"
  and "bounded_lattice.bot (test A) = 0"
  and "x \<sqsubseteq>\<^bsub>test A\<^esub> y \<longleftrightarrow> x \<sqsubseteq> y"
  by (simp_all add: test_ba test_one test_zero test_join test_meet test_join)

context kat
begin

  lemma test_le_var: "x \<sqsubseteq>\<^bsub>test A\<^esub> y \<longleftrightarrow> x \<sqsubseteq> y"
    by (metis (full_types) test_le)

  lemma rem_tj: "\<lbrakk>P (order.meet (test A) x y); x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> P (x \<cdot> y)"
    by (metis test_meet)

  lemma test_subset_var: "p \<in> tests A \<Longrightarrow> p \<in> carrier A"
    by (metis insert_absorb insert_subset test_subset)

  lemma test_ord: "order (test A)"
    apply (insert test_ba)
    by (simp add: boolean_algebra_def distributive_lattice_def lattice_def join_semilattice_def)

  lemma test_bl: "bounded_lattice (test A)"
    by (insert test_ba, simp add: boolean_algebra_def complemented_lattice_def)

  lemma test_js: "join_semilattice (test A)"
    by (insert test_bl, simp add: bounded_lattice_def lattice_def)

  lemma test_ms: "meet_semilattice (test A)"
    by (insert test_bl, simp add: bounded_lattice_def lattice_def)

  lemma test_lattice: "lattice (test A)"
    by (insert test_bl, simp add: bounded_lattice_def)

  lemma test_distributive: "distributive_lattice (test A)"
    by (insert test_ba, simp add: boolean_algebra_def)

  lemma test_complemented: "complemented_lattice (test A)"
    by (insert test_ba, simp add: boolean_algebra_def)

  lemma test_plus_closed [simp]: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x + y \<in> tests A"
    by (metis test.join_closed test_join)

  lemma test_mult_closed [simp]: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x\<cdot>y \<in> tests A"
    by (metis meet_closed test_meet)

  declare test_join [simp]
  declare test_meet [simp]
  declare test_le_var[simp]
  declare test_one[simp]
  declare test_zero[simp]

  lemma test_dist1:
    "\<lbrakk>x \<in> tests A; y \<in> tests A; z \<in> tests A\<rbrakk> \<Longrightarrow> x \<cdot> (y + z) = (x \<cdot> y) + (x \<cdot> z)"
    by (insert distributive_lattice.dist1[OF test_distributive], simp)

  lemma test_dist2:
    "\<lbrakk>x \<in> tests A; y \<in> tests A; z \<in> tests A\<rbrakk> \<Longrightarrow> x + y \<cdot> z = (x + y) \<cdot> (x + z)"
    by (insert distributive_lattice.dist2[OF test_distributive], simp)

  lemma test_join_closed: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x + y \<in> tests A"
    by (insert join_semilattice.join_closed[OF test_js], simp)

  lemma test_meet_closed: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> tests A"
    by (insert meet_semilattice.meet_closed[OF test_ms], simp)

  lemma test_absorb1: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x + x \<cdot> y = x"
    by (insert lattice.absorb1[OF test_lattice], simp)

  lemma test_absorb2: "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x \<cdot> (x + y) = x"
    by (insert lattice.absorb2[OF test_lattice], simp)

  lemma test_join_assoc:
    "\<lbrakk>x \<in> tests A; y \<in> tests A; z \<in> tests A\<rbrakk> \<Longrightarrow> (x + y) + z = x + (y + z)"
    by (insert join_semilattice.join_assoc[OF test_js], simp)

  lemma test_meet_assoc:
    "\<lbrakk>x \<in> tests A; y \<in> tests A; z \<in> tests A\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    by (insert meet_semilattice.meet_assoc[OF test_ms], simp)

  lemma test_join_idem: "x \<in> tests A \<Longrightarrow> x + x = x"
    by (insert join_semilattice.join_idem[OF test_js], simp)

  lemma test_meet_idem: "x \<in> tests A \<Longrightarrow> x \<cdot> x = x"
    by (insert meet_semilattice.meet_idem[OF test_ms], simp)

  lemma test_leq_def:
        "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y) = (x + y = y)"
    by (insert join_semilattice.leq_def[OF test_js], simp)

  lemma test_leq_meet_def:
        "\<lbrakk>x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y) = (x \<cdot> y = x)"
    by (insert meet_semilattice.leq_meet_def[OF test_ms], simp)

  lemma test_refl: "x \<in> tests A \<Longrightarrow> x \<sqsubseteq> x"
    by (insert order.order_refl[OF test_ord], simp)

  lemma test_trans:
    "\<lbrakk>x \<in> tests A; y \<in> tests A; z \<in> tests A; x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
    by (insert order.order_trans[OF test_ord,simplified,of x y z], auto)

  lemma test_antisym: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> tests A; y \<in> tests A\<rbrakk> \<Longrightarrow> x = y"
    by (insert order.order_antisym[OF test_ord], simp)

  lemma test_compl:
    "x \<in> tests A \<Longrightarrow> \<exists>y. y \<in> tests A \<and> x + y = 1 \<and> x \<cdot> y = 0"
    apply (insert complemented_lattice.compl[OF test_complemented], simp)
    by (metis test_join test_meet)

  lemma test_compl_uniq:
    "x \<in> tests A \<Longrightarrow> \<exists>!y. y \<in> tests A \<and> x + y = 1 \<and> x \<cdot> y = 0"
    apply (insert boolean_algebra.compl_uniq[OF test_ba], simp)
    by (metis test_join test_meet)

  lemmas test_one_closed = bounded_lattice.top_closed[OF test_bl, simplified]
    and test_zero_closed = bounded_lattice.bot_closed[OF test_bl, simplified]

  declare test_join_closed [simp del]
  declare test_meet_closed [simp del]
  declare test_join [simp del]
  declare test_meet [simp del]
  declare test_le_var [simp del]
  declare test_one [simp del]
  declare test_zero [simp del]

  definition complement :: "'a \<Rightarrow> 'a" ("!") where
    "complement x = (THE y. y \<in> tests A \<and> x + y = 1 \<and> x \<cdot> y = 0)"

  lemma complement_closed: assumes xc: "x \<in> tests A" shows "!x \<in> tests A"
    by (simp add: complement_def, rule the1I2, rule test_compl_uniq[OF xc], auto)

  lemma complement1: "p \<in> tests A \<Longrightarrow> p + !p = 1"
    by (simp add: complement_def, rule the1I2, rule test_compl_uniq[OF assms], auto+)

  lemma complement2: "p \<in> tests A \<Longrightarrow> p \<cdot> !p = 0"
    by (simp add: complement_def, rule the1I2, rule test_compl_uniq[OF assms], auto+)

  lemma test_mult_comm: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p\<cdot>q = q\<cdot>p"
    by (metis meet_comm test_meet)

  lemma test_under_one: "p \<in> tests A \<Longrightarrow> p \<sqsubseteq> 1"
    by (metis test_absorb2 test_compl_uniq test_leq_meet_def top_closed)

  lemma test_not_one: "!1 = 0"
    by (metis complement2 local.complement_closed mult_onel test_subset_var top_closed)

  lemma test_double_compl: "p \<in> tests A \<Longrightarrow> p = !(!p)"
    apply (simp add: complement_def)
    apply (rule the1I2)
    apply (simp_all add: complement_def[symmetric])
    apply (rule test_compl_uniq)
    apply (rule complement_closed[OF assms])
    apply auto
    by (smt add_comm complement1 complement2 complement_closed test_compl_uniq test_mult_comm test_subset_var)

  lemma de_morgan1: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> !p \<cdot> !q = !(p + q)"
    apply (subgoal_tac "p + q + !p\<cdot>!q = 1" "(p + q) \<cdot>(!p\<cdot>!q) = 0")
    apply (smt complement1 complement2 complement_closed test_compl_uniq test_join_closed test_meet_closed)
    apply (smt complement2 complement_closed mult_zeror test_dist1 test_join_closed test_meet_assoc test_meet_closed test_mult_comm test_subset_var)
    by (smt add_comm complement1 complement_closed nat_order_def test_absorb2 test_dist2 test_join_assoc test_join_closed test_subset_var test_under_one)

  lemma test_meet_def: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p \<cdot> q = !(!p + !q)"
    by (metis complement_closed de_morgan1 test_double_compl)

  lemma de_morgan2: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> !p + !q = !(p \<cdot> q)"
    by (smt complement_closed test_double_compl test_join_closed test_meet_def)

  lemma test_compl_anti: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p \<sqsubseteq> q \<longleftrightarrow> !q \<sqsubseteq> !p"
    by (metis add_idem de_morgan2 nat_order_def test_leq_meet_def test_meet_def test_mult_comm test_subset_var)

  lemma test_join_def: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p + q = !(!p \<cdot> !q)"
    by (metis de_morgan1 test_double_compl test_join_closed)

  lemma ba_1: "\<lbrakk>p \<in> tests A; q \<in> tests A; r \<in> tests A\<rbrakk> \<Longrightarrow> p + q + !q = r + !r"
    by (metis (lifting) complement1 complement_closed nat_order_def test_join_assoc test_under_one)

  lemma ba_2: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p + p = p + !(q + !q)"
    by (metis (lifting) add_zeror complement1 test_join_idem test_not_one test_subset_var)

  lemma ba_3: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p = (p \<cdot> q) + (p \<cdot> !q)"
    by (metis (lifting) complement1 complement_closed mult_oner test_dist1 test_subset_var)

  lemma ba_4: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> p = (p + !q) \<cdot> (p + q)"
    by (metis complement2 complement_closed dioid.add_zeror ka_dioid test_dist2 test_mult_comm test_subset_var)

  lemma ba_5: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> (p + q) \<cdot> !p = q \<cdot> !p"
    by (metis (lifting) complement2 complement_closed dioid.add_zerol distr ka_dioid mult_closed test_subset_var)

  lemma ba_6: "p \<in> tests A \<Longrightarrow>  !p\<cdot>p = 0"
    by (metis complement2 local.complement_closed test_mult_comm)

  lemma compl_1: "\<lbrakk>p \<in> tests A; q \<in> tests A\<rbrakk> \<Longrightarrow> !p = !(p + q) + !(p + !q)"
    by (metis (lifting) ba_3 complement_closed de_morgan1)
end
end