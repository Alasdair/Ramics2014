theory DRA
  imports Tests Kleene_Algebra_Left
begin

text {*
  A demoniac Refinement Algebra is a Kleene Algebra without right annihilation plus an iteration 
  operator (infinite iteration).
*}
class dra = kleene_algebra_zerol +
  fixes strong_iteration :: "'a \<Rightarrow> 'a" ("_\<^sup>\<infinity>" [101] 100)
  assumes iteration_unfoldl: "1 + x \<cdot> x\<^sup>\<infinity> = x\<^sup>\<infinity>"
  and iteration_inductl: "y \<le> z + x \<cdot> y \<longrightarrow> y \<le> x\<^sup>\<infinity> \<cdot> z"
  and isolation: "x\<^sup>\<infinity> = x\<^sup>\<star> + x\<^sup>\<infinity>\<cdot>0"
begin

text {* \<top> is an abort statement, defined is infinity skip *}
abbreviation top_elem :: "'a" ("\<top>") where "\<top> \<equiv> 1\<^sup>\<infinity>"

text {* Simple/basic lemmas about iteration operator *}

lemma iteration_refl: "1 \<le> x\<^sup>\<infinity>"
  by (metis add_ub1 iteration_unfoldl)

lemma top_ref: "x \<le> \<top>"
  by (metis add_idem' add_lub add_ub1 mult_1_left mult_1_right iteration_inductl)

lemma top_mult_annil: "\<top>\<cdot>x = \<top>"
  by (metis add_ub2 eq_iff mult_1_left iteration_inductl top_ref)

lemma top_add_annil: "\<top> + x = \<top>"
  by (metis add_commute less_eq_def top_ref)

lemma top_elim: "x\<cdot>y \<le> x\<cdot>\<top>"
  by (metis mult_isol top_ref)  

lemma iteration_unfoldl_distl: "y\<cdot>x\<^sup>\<infinity> = y + y\<cdot>x\<cdot>x\<^sup>\<infinity>"
  by (metis distrib_left mult_assoc mult_oner iteration_unfoldl)

lemma iteration_unfoldl_distr: "x\<^sup>\<infinity>\<cdot>y = y + x\<cdot>x\<^sup>\<infinity>\<cdot>y"
  by (metis distrib_right' mult_1_left iteration_unfoldl)

lemma iteration_unfoldl': "z\<cdot>x\<^sup>\<infinity>\<cdot>y = z\<cdot>y + z\<cdot>x\<cdot>x\<^sup>\<infinity>\<cdot>y"
  by (metis distrib_left mult_assoc iteration_unfoldl_distr)

lemma iteration_idem: "x\<^sup>\<infinity> = x\<^sup>\<infinity>\<cdot>x\<^sup>\<infinity>"
  by (smt add_zerol annil isolation mult_assoc iteration_refl iteration_unfoldl_distr star_inductl_var_eq2 star_invol star_sum_unfold sup_id_star1)

lemma iteration_induct: "x\<cdot>x\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>x"
  by (metis eq_iff mult_assoc iteration_inductl iteration_unfoldl_distl)

lemma iteration_ref_star: "x\<^sup>\<star> \<le> x\<^sup>\<infinity>"
  by (metis eq_refl iteration_unfoldl star_inductl_one)

lemma iteration_subdist: "x\<^sup>\<infinity> \<le> (x + y)\<^sup>\<infinity>"
  by (metis add_assoc' distrib_right' mult_oner iteration_inductl add_ub1 iteration_unfoldl)

lemma iteration_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<infinity> \<le> y\<^sup>\<infinity>"
  by (metis iteration_subdist order_prop)

lemma iteration_unfoldr: "1 + x\<^sup>\<infinity> \<cdot> x = x\<^sup>\<infinity>"
  by (metis add_0_left annil eq_refl isolation mult_assoc iteration_idem iteration_unfoldl iteration_unfoldl_distr star_denest star_one star_prod_unfold star_slide tc)

lemma iteration_unfoldr_distl: "y\<cdot>x\<^sup>\<infinity> = y + y\<cdot>x\<^sup>\<infinity>\<cdot>x"
  by (metis distrib_left mult_assoc mult_oner iteration_unfoldr)

lemma iteration_unfoldr_distr: "x\<^sup>\<infinity>\<cdot>y = y + x\<^sup>\<infinity>\<cdot>x\<cdot>y"
  by (metis iteration_unfoldl_distr iteration_unfoldr_distl)

lemma iteration_unfoldr': "z\<cdot>x\<^sup>\<infinity>\<cdot>y = z\<cdot>y + z\<cdot>x\<^sup>\<infinity>\<cdot>x\<cdot>y"
  by (metis distrib_left mult_assoc iteration_unfoldr_distr)

lemma iteration_double: "(x\<^sup>\<infinity>)\<^sup>\<infinity> = \<top>"
  by (metis less_eq_def iteration_iso iteration_refl top_add_annil)

lemma star_iteration: "(x\<^sup>\<star>)\<^sup>\<infinity> = \<top>"
  by (metis less_eq_def iteration_iso star_ref top_add_annil)

lemma iteration_star: "(x\<^sup>\<infinity>)\<^sup>\<star> = x\<^sup>\<infinity>"
  by (metis boffa less_eq_def iteration_idem iteration_refl)

lemma iteration_star2: "x\<^sup>\<infinity> = x\<^sup>\<star>\<cdot>x\<^sup>\<infinity>"
  by (metis add_assoc boffa isolation mult_1_right iteration_idem iteration_unfoldl star_denest star_denest_var_2 star_invol star_slide star_zero)

lemma iteration_zero: "0\<^sup>\<infinity> = 1"
  by (metis add_zeror annil iteration_unfoldl)

lemma iteration_subdenest: "x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity> \<le> (x + y)\<^sup>\<infinity>"
  by (metis add_commute mult_isol_var iteration_idem iteration_subdist)

text {* Important DRA properties *}

text {* Sliding laws (leapfrog) *}
lemma iteration_slide: "x\<cdot>(y\<cdot>x)\<^sup>\<infinity> = (x\<cdot>y)\<^sup>\<infinity>\<cdot>x"
proof -
  have "y\<cdot>(x\<cdot>y)\<^sup>\<infinity>\<cdot>x \<le> (y\<cdot>x)\<^sup>\<infinity>\<cdot>y\<cdot>x"
    by (metis mult_assoc mult_isor iteration_inductl iteration_unfoldl_distr iteration_unfoldr_distl order_refl)
  hence "y\<cdot>(x\<cdot>y)\<^sup>\<infinity>\<cdot>x + 1 \<le> (y\<cdot>x)\<^sup>\<infinity>"
    by (smt add_assoc' add_commute eq_refl mult_assoc iteration_unfoldr add_comm add_idem' less_eq_def)
  hence "x\<cdot>y\<cdot>(x\<cdot>y)\<^sup>\<infinity>\<cdot>x + x \<le> x\<cdot>(y\<cdot>x)\<^sup>\<infinity>"
    by (metis add_lub add_ub1 mult_assoc mult_isol iteration_unfoldl_distl)
  hence "(x\<cdot>y)\<^sup>\<infinity>\<cdot>x \<le> x\<cdot>(y\<cdot>x)\<^sup>\<infinity>"
    by (metis add_commute iteration_unfoldl_distr)
  thus ?thesis
    by (metis eq_iff mult_assoc iteration_inductl iteration_unfoldl_distl)
qed

lemma star_iteration_slide: "(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity> = y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity>"
proof -
  have "y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity> \<le> 1 + (x\<^sup>\<star>\<cdot>y)\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity> + x\<^sup>\<star>\<cdot>y\<cdot>y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity>"
    by (metis star_unfoldl_eq distrib_right' eq_refl iteration_unfoldl star_ref mult_1_left mult_isor add_iso_var)
  hence "y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity> \<le> 1 + x\<^sup>\<star>\<cdot>y\<cdot>y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity>"
    by (metis less_eq_def add_assoc distrib_left distrib_right mult_1_left mult_assoc star_ref)
  thus ?thesis
    by (metis mult_1_right mult_assoc iteration_inductl star_ref mult_1_left mult_isor add_commute less_eq_def)
qed

text {* Denesting laws (decomposition) *}

lemma iteration_denest: "(x + y)\<^sup>\<infinity> = x\<^sup>\<infinity>\<cdot>(y\<cdot>x\<^sup>\<infinity>)\<^sup>\<infinity>"
proof -
  have "x\<^sup>\<infinity>\<cdot>(y\<cdot>x\<^sup>\<infinity>)\<^sup>\<infinity> \<le> x\<cdot>x\<^sup>\<infinity>\<cdot>(y\<cdot>x\<^sup>\<infinity>)\<^sup>\<infinity> + y\<cdot>x\<^sup>\<infinity>\<cdot>(y\<cdot>x\<^sup>\<infinity>)\<^sup>\<infinity> + 1"
    by (metis eq_refl iteration_unfoldl_distr add_comm add_left_commute iteration_unfoldl)
  moreover hence "x\<^sup>\<infinity>\<cdot>(y\<cdot>x\<^sup>\<infinity>)\<^sup>\<infinity> \<le> (x + y)\<^sup>\<infinity>"
    by (metis add_commute distrib_right mult_1_right mult_assoc iteration_inductl)
  moreover have "(x + y)\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>(y\<cdot>(x + y)\<^sup>\<infinity> + 1)"
    by (smt add_assoc add_commute distrib_right eq_refl iteration_unfoldl iteration_inductl)
  moreover hence "y\<cdot>(x + y)\<^sup>\<infinity> + 1 \<le> y\<cdot>x\<^sup>\<infinity>\<cdot>(y\<cdot>(x + y)\<^sup>\<infinity> + 1) + 1"
    by (metis add_iso_var eq_refl mult_assoc mult_isol)
  moreover hence "x\<^sup>\<infinity>\<cdot>(y\<cdot>(x + y)\<^sup>\<infinity> + 1) \<le> x\<^sup>\<infinity>\<cdot>(y\<cdot>x\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis add_commute mult_oner iteration_inductl mult_isol)
  ultimately show ?thesis
    by (metis order_trans add_commute less_eq_def)
qed

lemma iteration_denest2: "(x + y)\<^sup>\<infinity> = y\<^sup>\<star>\<cdot>x\<cdot>(x + y)\<^sup>\<infinity> + y\<^sup>\<infinity>"
proof -
  have "(x + y)\<^sup>\<infinity> = y\<^sup>\<infinity>\<cdot>x\<cdot>(y\<^sup>\<infinity>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity> + y\<^sup>\<infinity>"
    by (metis add_commute iteration_denest iteration_slide iteration_unfoldl_distr)
  also have "... = y\<^sup>\<star>\<cdot>x\<cdot>(y\<^sup>\<infinity>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity> + y\<^sup>\<infinity>\<cdot>0 + y\<^sup>\<infinity>"
    by (metis isolation mult_assoc distrib_right' annil mult_assoc)
  also have "... = y\<^sup>\<star>\<cdot>x\<cdot>(y\<^sup>\<infinity>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity> + y\<^sup>\<infinity>"
    by (metis add_assoc distrib_left mult_1_right add_0_left mult_1_right)
  finally show ?thesis
    by (metis add_commute iteration_denest iteration_slide mult_assoc)
qed

lemma iteration_denest3: "(x + y)\<^sup>\<infinity> = (y\<^sup>\<star>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
  apply (rule antisym, metis add_commute iteration_denest2 eq_refl iteration_inductl)
  by (smt add_commute iteration_denest iteration_slide mult_isor iteration_iso iteration_ref_star)

text {* Simulation laws (for Data Refinement) *}

lemma iteration_sim: "z\<cdot>y \<le> x\<cdot>z \<Longrightarrow> z\<cdot>y\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>z"
  by (metis add_commute iteration_unfoldl_distl add_iso mult_isor mult_assoc iteration_inductl)

lemma "y\<cdot>z \<le> z\<cdot>x \<Longrightarrow> y\<^sup>\<infinity>\<cdot>z \<le> z\<cdot>x\<^sup>\<infinity>"
  nitpick oops

text {* Separation laws (reasoning about distributed systems) *}

lemma iteration_sep: "y\<cdot>x \<le> x\<cdot>y \<Longrightarrow> (x + y)\<^sup>\<infinity> = x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
proof -
  assume "y\<cdot>x \<le> x\<cdot>y"
  hence "y\<^sup>\<star>\<cdot>x \<le> x\<cdot>(x + y)\<^sup>\<star>"
    by (metis star_sim1 add_commute mult_isol order_trans star_subdist)
  hence "y\<^sup>\<star>\<cdot>x\<cdot>(x + y)\<^sup>\<infinity> + y\<^sup>\<infinity> \<le> x\<cdot>(x + y)\<^sup>\<infinity> + y\<^sup>\<infinity>"
    by (metis mult_isor mult_assoc iteration_star2 add_iso_var eq_refl)
  thus ?thesis
    by (metis iteration_denest2 add_commute iteration_inductl add_commute less_eq_def iteration_subdenest)
qed

lemma iteration_sim2: "y\<cdot>x \<le> x\<cdot>y \<Longrightarrow> y\<^sup>\<infinity>\<cdot>x\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
  by (metis add_commute iteration_sep iteration_subdenest)

lemma iteration_sep2: "y\<cdot>x \<le> x\<cdot>y\<^sup>\<star> \<Longrightarrow> (x + y)\<^sup>\<infinity> = x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
proof - 
  assume "y\<cdot>x \<le> x\<cdot>y\<^sup>\<star>"
  hence "y\<^sup>\<star>\<cdot>(y\<^sup>\<star>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>y\<^sup>\<star>\<cdot>y\<^sup>\<infinity>"
    by (metis mult_assoc mult_isor iteration_sim star_denest_var_2 star_sim1 star_slide_var star_trans_eq tc_eq)
  moreover have "x\<^sup>\<infinity>\<cdot>y\<^sup>\<star>\<cdot>y\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
    by (metis eq_refl mult_assoc iteration_star2)
  moreover have "(y\<^sup>\<star>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity> \<le> y\<^sup>\<star>\<cdot>(y\<^sup>\<star>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
    by (metis mult_isor mult_onel star_ref)
  ultimately show ?thesis
    by (metis antisym iteration_denest3 iteration_subdenest order_trans)
qed

lemma iteration_sep3: "y\<cdot>x \<le> x\<cdot>(x + y) \<Longrightarrow> (x + y)\<^sup>\<infinity> = x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
proof -
  assume "y\<cdot>x \<le> x\<cdot>(x + y)"
  hence "y\<^sup>\<star>\<cdot>x \<le> x\<cdot>(x + y)\<^sup>\<star>"
    by (metis star_sim1)
  hence "y\<^sup>\<star>\<cdot>x\<cdot>(x + y)\<^sup>\<infinity> + y\<^sup>\<infinity> \<le> x\<cdot>(x + y)\<^sup>\<star>\<cdot>(x + y)\<^sup>\<infinity> + y\<^sup>\<infinity>"
    by (metis add_iso mult_isor)
  hence "(x + y)\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
    by (metis mult_assoc iteration_denest2 iteration_star2 add_commute iteration_inductl)
  thus ?thesis
    by (metis add_commute less_eq_def iteration_subdenest)
qed

lemma iteration_sep4: "\<lbrakk>y\<cdot>0 = 0; z\<cdot>x = 0; y\<cdot>x \<le> (x + z)\<cdot>y\<^sup>\<star>\<rbrakk> \<Longrightarrow> (x + y + z)\<^sup>\<infinity> = x\<^sup>\<infinity>\<cdot>(y + z)\<^sup>\<infinity>"
proof -
  assume assms: "y\<cdot>0 = 0" "z\<cdot>x = 0" "y\<cdot>x \<le> (x + z)\<cdot>y\<^sup>\<star>"
  have "y\<cdot>y\<^sup>\<star>\<cdot>z \<le> y\<^sup>\<star>\<cdot>z\<cdot>y\<^sup>\<star>"
    by (metis mult_isor star_1l mult_oner order_trans star_plus_one subdistl)
  have "y\<^sup>\<star>\<cdot>z\<cdot>x \<le> x\<cdot>y\<^sup>\<star>\<cdot>z"
    by (metis zero_least assms(1) assms(2) independence1 mult_assoc)
  have "y\<cdot>(x + y\<^sup>\<star>\<cdot>z) \<le> (x + z)\<cdot>y\<^sup>\<star> + y\<cdot>y\<^sup>\<star>\<cdot>z"
    by (metis assms(3) distrib_left mult_assoc add_iso)
  also have "... \<le> (x + y\<^sup>\<star>\<cdot>z)\<cdot>y\<^sup>\<star> + y\<cdot>y\<^sup>\<star>\<cdot>z" 
    by (metis star_ref add_iso_var eq_refl mult_1_left mult_isor)
  also have "... \<le> (x + y\<^sup>\<star>\<cdot>z)\<cdot>y\<^sup>\<star> + y\<^sup>\<star>\<cdot>z \<cdot>y\<^sup>\<star>" using `y\<cdot>y\<^sup>\<star>\<cdot>z \<le> y\<^sup>\<star>\<cdot>z\<cdot>y\<^sup>\<star>`
    by (metis add_commute add_iso)
  finally have "y\<cdot>(x + y\<^sup>\<star>\<cdot>z) \<le> (x + y\<^sup>\<star>\<cdot>z)\<cdot>y\<^sup>\<star>"
    by (metis add_commute add_idem' add_left_commute distrib_right)
  moreover have "(x + y + z)\<^sup>\<infinity> \<le> (x + y + y\<^sup>\<star>\<cdot>z)\<^sup>\<infinity>"
    by (metis star_ref add_iso_var eq_refl mult_1_left mult_isor iteration_iso)  
  moreover have "... = (x + y\<^sup>\<star>\<cdot>z)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
    by (metis add_assoc add_commute calculation iteration_sep2)
  moreover have "... = x\<^sup>\<infinity>\<cdot>(y\<^sup>\<star>\<cdot>z)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>" using `y\<^sup>\<star>\<cdot>z\<cdot>x \<le> x\<cdot>y\<^sup>\<star>\<cdot>z`
    by (metis iteration_sep mult_assoc)
  ultimately have "(x + y + z)\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>(y + z)\<^sup>\<infinity>"
    by (metis add_commute mult_assoc iteration_denest3)
  thus ?thesis
    by (metis add_commute add_left_commute less_eq_def iteration_subdenest)
qed

text {* Idependence (blocking) laws *}
lemma "x\<cdot>y = 0 \<Longrightarrow> x\<^sup>\<infinity>\<cdot>y = y"
  nitpick oops

lemma iteration_idep: "x\<cdot>y = 0 \<Longrightarrow> x\<cdot>y\<^sup>\<infinity> = x"
  by (metis add_zeror annil iteration_unfoldl_distl)

lemma iteration_bubble_sort: "y\<cdot>x \<le> x\<cdot>y \<Longrightarrow> (x + y)\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
  by (metis eq_iff iteration_sep)

end

class dra_tests = dra + dioid_tests
begin

text {*
  Assertions is a mapping from guards to a subset similar to tests, but abort if the predicate does
  not hold.
*}
definition assertion :: "'a \<Rightarrow> 'a" ("_\<^sup>o" [101] 100) where
  "test p \<Longrightarrow> p\<^sup>o = !p\<cdot>\<top> + 1"

lemma asg: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> q \<le> 1 \<and> 1 \<le> p\<^sup>o"
  by (metis add_commute add_ub1 assertion_def test_ub_var)

lemma assertion_isol: "test p \<Longrightarrow> y \<le> p\<^sup>o\<cdot>x \<longleftrightarrow> p\<cdot>y \<le> x"
proof
  assume assms: "test p" "y \<le> p\<^sup>o\<cdot>x"
  hence "p\<cdot>y \<le> p\<cdot>(!p\<cdot>\<top> + 1)\<cdot>x"
    by (metis mult_assoc mult_isol assertion_def assms(1))
  also have "... = p\<cdot>!p\<cdot>\<top>\<cdot>x + p\<cdot>x"
    by (metis distrib_left distrib_right' mult_1_left mult_assoc)
  also have "... \<le> x"
    by (metis assms(1) distrib_right' mult_assoc add_zerol annil test_comp_mult eq_refl test_eq1)
  finally show "p\<cdot>y \<le> x"
    by metis
next
  assume assms: "test p" "p\<cdot>y \<le> x"
  hence "p\<^sup>o\<cdot>p\<cdot>y = !p\<cdot>\<top>\<cdot>p\<cdot>y + p\<cdot>y"
    by (metis assertion_def distrib_right' mult_1_left mult_assoc)
  also have "... = !p\<cdot>\<top> + p\<cdot>y"
    by (metis mult_assoc top_mult_annil)
  moreover have "p\<^sup>o\<cdot>p\<cdot>y \<le> p\<^sup>o\<cdot>x"
    by (metis assms(2) mult_assoc mult_isol)
  moreover have "!p\<cdot>y + p\<cdot>y \<le> !p\<cdot>\<top> + p\<cdot>y"
    by (metis add_commute assms(1) order_refl test_eq2 top_elim)
  ultimately show "y \<le> p\<^sup>o\<cdot>x"
    by (metis add_commute assms(1) distrib_right' mult_1_left order_trans test_comp_add)
qed

lemma assertion_isor: "test p \<Longrightarrow> y \<le> x\<cdot>p \<longleftrightarrow> y\<cdot>p\<^sup>o \<le> x"
proof
  assume assms: "test p" "y \<le> x\<cdot>p"
  hence "y\<cdot>p\<^sup>o \<le> x\<cdot>p\<cdot>!p\<cdot>\<top> + x\<cdot>p"
    by (metis mult_isor assertion_def assms(1) distrib_left mult_1_right mult_assoc)
  also have "... \<le> x"
    by (metis assms(1) add_zerol annil distrib_left mult_assoc test_comp_mult distrib_left mult_1_right order_prop test_comp)
  finally show "y\<cdot>p\<^sup>o \<le> x"
    by metis
next
  assume assms: "test p" "y\<cdot>p\<^sup>o \<le> x"
  have "y \<le> y\<cdot>(!p\<cdot>\<top> + p)"
    by (metis add_iso_var mult_isol order_refl order_refl top_elim add_commute assms(1) mult_1_right test_comp_add)
  also have "... = y\<cdot>p\<^sup>o\<cdot>p"
    by (metis assertion_def assms(1) distrib_right' mult_1_left mult_assoc top_mult_annil)
  finally show "y \<le> x\<cdot>p"
    by (metis assms(2) mult_isor order_trans)
qed

lemma assertion_iso: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> x\<cdot>q\<^sup>o \<le> p\<^sup>o\<cdot>x \<longleftrightarrow> p\<cdot>x \<le> x\<cdot>q"
  by (metis assertion_isol assertion_isor mult_assoc)

lemma total_correctness: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p\<cdot>x\<cdot>!q = 0 \<longleftrightarrow> x\<cdot>!q \<le> !p\<cdot>\<top>"
  apply (default, metis mult_assoc test_eq1 top_elim zero_least)
  by (metis annil test_comp_mult zero_unique mult_assoc mult_isol)

lemma test_iteration_sim: "\<lbrakk>test p; p\<cdot>x \<le> x\<cdot>p\<rbrakk> \<Longrightarrow> p\<cdot>x\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>p"
  by (metis iteration_sim)

lemma test_iteration_annir: "test p \<Longrightarrow> !p\<cdot>(p\<cdot>x)\<^sup>\<infinity> = !p"
  by (metis annil ba6 iteration_idep mult_assoc)

text {* Example of program transformation *}

lemma loop_refinement: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p\<cdot>x)\<^sup>\<infinity>\<cdot>!p \<le> (p\<cdot>q\<cdot>x)\<^sup>\<infinity>\<cdot>!(p\<cdot>q)\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p"
proof -
  assume assms: "test p" "test q"
  hence one: "p\<cdot>q\<cdot>p\<cdot>x\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p + p\<cdot>q\<cdot>!p = p\<cdot>q\<cdot>x\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p"
    by (metis assms test2 test3 add_zeror)
  hence "p\<cdot>q\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p \<le> p\<cdot>q\<cdot>x\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p \<and> !(p\<cdot>q)\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p \<le> !(p\<cdot>q)\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p"
    by (metis eq_refl distrib_left mult_assoc iteration_unfoldl_distr add_commute)
  hence "(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p \<le> p\<cdot>q\<cdot>x\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p + !(p\<cdot>q)\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p"
    by (smt add_commute add_ub1 assms distrib_left mult_assoc iteration_slide iteration_unfoldr_distr one test_eq1 test_mult_closed)
  thus ?thesis
    by (metis iteration_inductl add_commute mult_assoc)
qed

text {* Back's atomicity refinement theorem for action systems *}

lemma atom_step1: "r\<cdot>b \<le> b\<cdot>r \<Longrightarrow> (a + b + r)\<^sup>\<infinity> = b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
  by (smt add_commute iteration_denest mult_assoc iteration_sep)

lemma atom_step2: 
  assumes "s = s\<cdot>q" "q\<cdot>b = 0" "r\<cdot>q \<le> q\<cdot>r" "q\<cdot>l \<le> l\<cdot>q" "r\<^sup>\<infinity> = r\<^sup>\<star>" "test q"
  shows "s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q)\<^sup>\<infinity> \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
proof -
  have "s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q)\<^sup>\<infinity> \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis assms(3) assms(5) star_sim1 mult_assoc mult_isol iteration_iso)
  also have "... \<le> s\<cdot>q\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis assms(1,6) test_ub_var mult_double_iso mult_oner)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>q\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis assms(4) iteration_sim mult_assoc mult_double_iso)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis assms(2) iteration_idep mult_assoc order_refl)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis assms(6) test_ub_var mult_double_iso mult_isor mult_oner)
  finally show "s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q)\<^sup>\<infinity> \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by metis
qed

lemma atom_step3: 
  assumes "r\<cdot>l \<le> l\<cdot>r" "a\<cdot>l \<le> l\<cdot>a" "b\<cdot>l \<le> l\<cdot>b" "q\<cdot>l \<le> l\<cdot>q" "b\<^sup>\<infinity> = b\<^sup>\<star>"
  shows "l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity> = (a\<cdot>b\<^sup>\<infinity>\<cdot>q + l + r)\<^sup>\<infinity>"
proof -
  have "(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r)\<cdot>l \<le> a\<cdot>b\<^sup>\<infinity>\<cdot>l\<cdot>q + l\<cdot>r"
    by (metis distrib_right add_iso_var assms(1,4) mult_assoc mult_isol)
  also have "... \<le> a\<cdot>l\<cdot>b\<^sup>\<infinity>\<cdot>q + l\<cdot>r"
    by (metis assms(3) assms(5) star_sim1 add_iso mult_assoc mult_double_iso)
  also have "... \<le> l\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r)"
    by (smt add_assoc' add_ub2 assms(2) distrib_left distrib_right' less_eq_def mult_assoc)
  finally have "(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r)\<cdot>l \<le> l\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r)"
    by metis
  moreover have "l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity> = l\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r)\<^sup>\<infinity>"
    by (metis add_commute mult_assoc iteration_denest)
  ultimately show ?thesis
    by (metis add_commute add_left_commute iteration_sep)
qed

theorem atom_ref_back: 
  assumes "s = s\<cdot>q" "a = q\<cdot>a" "q\<cdot>b = 0"
          "r\<cdot>b \<le> b\<cdot>r" "r\<cdot>l \<le> l\<cdot>r" "r\<cdot>q \<le> q\<cdot>r"
          "a\<cdot>l \<le> l\<cdot>a" "b\<cdot>l \<le> l\<cdot>b" "q\<cdot>l \<le> l\<cdot>q"
          "r\<^sup>\<infinity> = r\<^sup>\<star>" "b\<^sup>\<infinity> = b\<^sup>\<star>" "test q"
  shows "s\<cdot>(a + b + r + l)\<^sup>\<infinity>\<cdot>q \<le> s\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r + l)\<^sup>\<infinity>"
proof -
  have "(a + b + r)\<cdot>l \<le> l\<cdot>(a + b + r)"
    by (smt assms add_lub add_ub2 distrib_right less_eq_def subdistl)
  hence "s\<cdot>(l + a + b + r)\<^sup>\<infinity>\<cdot>q = s\<cdot>l\<^sup>\<infinity>\<cdot>(a + b + r)\<^sup>\<infinity>\<cdot>q"
    by (metis add_commute add_left_commute mult_assoc iteration_sep)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q)\<^sup>\<infinity>"
    by (smt assms atom_step1 iteration_slide eq_refl mult_assoc)
  also have "... \<le> s\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + l + r)\<^sup>\<infinity>"
    by (smt assms eq_refl mult_assoc iteration_slide atom_step2 atom_step3)
  finally show ?thesis
    by (metis add_commute add_left_commute)
qed

text {* Cohen variation of the atomicity refinement theorem *}

lemma atom_ref_cohen: 
  assumes "r\<cdot>p\<cdot>y \<le> y\<cdot>r" "y\<cdot>p\<cdot>l \<le> l\<cdot>y" "r\<cdot>p\<cdot>l \<le> l\<cdot>r"
          "p\<cdot>r\<cdot>!p = 0" "p\<cdot>l\<cdot>!p = 0" "!p\<cdot>l\<cdot>p = 0"
          "y\<cdot>0 = 0" "r\<cdot>0 = 0" "test p"
  shows "(y + r + l)\<^sup>\<infinity> = (p\<cdot>l)\<^sup>\<infinity>\<cdot>(y + !p\<cdot>l + r\<cdot>!p)\<^sup>\<infinity>\<cdot>(r\<cdot>p)\<^sup>\<infinity>"
proof -    
  have "(y + r)\<cdot>p\<cdot>l \<le> l\<cdot>y + l\<cdot>r"
    by (smt add_lub add_ub2 assms(2) assms(3) distrib_right less_eq_def) 
  hence stepA: "(y + r)\<cdot>p\<cdot>l \<le> (p\<cdot>l + !p\<cdot>l)\<cdot>(y + r)\<^sup>\<star>"
    by (metis assms(9) distrib_left distrib_right' mult_1_left mult_isol order_trans star_ext test_comp_add)
  have "r\<cdot>p\<cdot>(y + r\<cdot>!p + !p\<cdot>l) \<le> y\<cdot>(r\<cdot>p + r\<cdot>!p)"
    by (metis assms(1,4,9) distrib_left add_0_left add_commute annil mult_assoc test_comp_mult distrib_left mult_oner test_comp_add)
  also have "... \<le> (y + r\<cdot>!p + !p\<cdot>l)\<cdot>(r\<cdot>p + (y + r\<cdot>!p + !p\<cdot>l))"
    by (smt add_lub add_ub1 add_ub2 mult_isol_var)
  finally have "r\<cdot>p\<cdot>(y + r\<cdot>!p + !p\<cdot>l) \<le> (y + r\<cdot>!p + !p\<cdot>l)\<cdot>(r\<cdot>p + (y + r\<cdot>!p + !p\<cdot>l))" 
    by metis  
  hence stepB: "(!p\<cdot>l + y + p\<cdot>r + !p\<cdot>r)\<^sup>\<infinity> = (y + !p\<cdot>l + r\<cdot>!p)\<^sup>\<infinity>\<cdot>(r\<cdot>p)\<^sup>\<infinity>"
    by (smt add_assoc add_commute assms iteration_sep3[of "r\<cdot>p" "y + r\<cdot>!p + !p\<cdot>l"] combine_common_factor distrib_left mult_1_left mult_1_right test_comp_add)
  have "(y + r + l)\<^sup>\<infinity> = (p\<cdot>l + !p\<cdot>l + y + r)\<^sup>\<infinity>"
    by (metis add_comm add_left_commute assms(9) distrib_right' mult_onel test_comp_add)
  also have "... = (p\<cdot>l)\<^sup>\<infinity>\<cdot>(!p\<cdot>l + y + r)\<^sup>\<infinity>" using stepA
    by (metis assms(6-8) annil add_assoc add_0_left distrib_right' add_commute mult_assoc iteration_sep4[of "y+r" "!p\<cdot>l" "p\<cdot>l"])
  also have "... = (p\<cdot>l)\<^sup>\<infinity>\<cdot>(!p\<cdot>l + y + p\<cdot>r + !p\<cdot>r)\<^sup>\<infinity>"
    by (metis add_commute assms(9) combine_common_factor mult_1_left test_comp_add)
  finally show ?thesis using stepB
    by (metis mult_assoc)
qed
end

end
