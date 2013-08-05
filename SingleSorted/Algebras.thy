theory Algebras
  imports OrderTheory
begin

no_notation
  Transitive_Closure.trancl ("(_\<^sup>+)" [1000] 999) and
  Transitive_Closure.rtrancl ("(_\<^sup>*)" [1000] 999)

(**************************************************************************)

section {* Operators *}

class mult_op =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70)

class c_mult_op =
  fixes c_mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<parallel>" 70)

class transcl_op =
  fixes transcl :: "'a \<Rightarrow> 'a" ("_\<^sup>+" [101] 100)

class star_op =
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>*" [101] 100)

class c_transcl_op =
  fixes c_transcl :: "'a \<Rightarrow> 'a" ("_\<^sup>\<oplus>" [101] 100)

class c_star_op =
  fixes c_star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<otimes>" [101] 100)

class invariant_op =
  fixes invariant :: "'a \<Rightarrow> 'a" ("\<iota>_" [101] 100)

(***********************************************************************)

section {* Semigroups and Bisemigroups *}

class semigroup_mult = mult_op +
  assumes mult_assoc [intro]: "(x\<cdot>y)\<cdot>z = x\<cdot>(y\<cdot>z)"

class ordered_semigroup_mult = semigroup_mult + order +
  assumes mult_isor [intro]: "x \<le> y \<Longrightarrow> z\<cdot>x \<le> z\<cdot>y"
  and  mult_isol [intro]: "x \<le> y \<Longrightarrow> x\<cdot>z \<le> y\<cdot>z"

class semigroup_add = plus +
  assumes add_assoc [intro]: "(x + y) + z = x + (y + z)"

class comm_semigroup_add = semigroup_add +
  assumes add_comm [intro]: "x + y = y + x"

class idem_semigroup_add = semigroup_add +
  assumes add_idem [simp]: "x + x = x"

class ordered_comm_semigroup_add = comm_semigroup_add + ord + 
  assumes leq_def [simp]: "x \<le> y \<longleftrightarrow> x + y = y"
  and strict_leq_def [simp]: "x < y \<longleftrightarrow> x \<le> y \<and> \<not>(y \<le> x)"

class idem_comm_semigroup_add = ordered_comm_semigroup_add + idem_semigroup_add
begin

subclass order
proof (unfold_locales)
  fix x y z
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (metis strict_leq_def)
  show "x \<le> x"
    by (metis add_idem leq_def)
  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z"
    by (metis add_assoc leq_def)
  show "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y"
    by (metis add_comm leq_def)
qed

lemma ex_lub_dioid: "is_lub (x + y) {x, y}"
  apply (simp add: is_lub_def is_ub_def)
  by (metis add_assoc add_comm add_idem)

subclass join_semilattice
  by (unfold_locales, metis ex_lub_dioid)

lemma join_plus_equiv [simp]: "x \<squnion> y = x + y"
  by (metis ex_lub_dioid join_def lub_is_lub)

lemma order_prop: "(x \<le> y) \<longleftrightarrow> (\<exists>z.(x + z = y))"
  by (metis add_assoc add_idem leq_def)

lemma add_lub: "x + y \<le> z \<longleftrightarrow> x \<le> z \<and> y \<le> z"
  by (metis add_assoc add_comm leq_def order_prop)

end

class semigroup_c_mult = c_mult_op + 
  assumes c_mult_assoc [intro]: "(x\<parallel>y)\<parallel>z = x\<parallel>(y\<parallel>z)"

class comm_semigroup_c_mult = semigroup_c_mult + 
  assumes c_mult_comm [intro]: "x\<parallel>y = y\<parallel>x"
begin

lemma c_mult_comml: "y\<parallel>(x\<parallel>z) = x\<parallel>(y\<parallel>z)"
proof -
  have "(y\<parallel>x)\<parallel>z = (x\<parallel>y)\<parallel>z"
    by (simp only: c_mult_comm)
  thus ?thesis
    by (simp only: c_mult_assoc)
qed  

end

text {* Of course, in an ordered bisemigroup, $\<parallel>$ should also be
isotone. *}

class ordered_comm_semigroup_c_mult = comm_semigroup_c_mult + order +
  assumes c_mult_isor [intro]: "x \<le> y \<Longrightarrow> z\<parallel>x \<le> z\<parallel>y"
begin
lemma c_mult_isol [intro]: "x \<le> y \<Longrightarrow> x\<parallel>z \<le> y\<parallel>z"
  by (metis c_mult_comm c_mult_isor)
end

text {* A bisemigroup is defined as a structure $(S,\<cdot>,\<parallel>)$ such that
$(S,\<cdot>)$ is a semigroup and $(S,\<parallel>)$ is a commutative semigroup. *}

class bisemigroup = semigroup_mult + comm_semigroup_c_mult

class ordered_bisemigroup = ordered_semigroup_mult + ordered_comm_semigroup_c_mult
begin
subclass bisemigroup
  by (unfold_locales)
end


(***********************************************************************)

section {* Monoids and Bimonoids *}

class monoid_mult = semigroup_mult + one +
  assumes mult_onel [simp]: "1\<cdot>x = x"
  and mult_oner [simp]: "x\<cdot>1 = x"

class ordered_monoid_mult = ordered_semigroup_mult + monoid_mult

class comm_monoid_add = comm_semigroup_add + zero + 
  assumes add_zerol [simp]: "0+x = x"
begin
lemma add_zeror [simp]: "x+0 = x"
  by (metis add_comm add_zerol)
end

class idem_comm_monoid_add = comm_monoid_add + idem_comm_semigroup_add
begin
subclass join_semilattice_zero
  by (unfold_locales, simp)

lemma add_iso: "x \<le> y \<longrightarrow> x + z \<le> y + z"
  by (metis join_iso join_plus_equiv)

lemma add_ub: "x \<le> x + y"
  by (metis join_plus_equiv join_ub)

lemma add_lub: "x + y \<le> z \<longleftrightarrow> x \<le> z \<and> y \<le> z"
  by (metis join_plus_equiv join_lub)

lemma add_un: "is_lub w A \<Longrightarrow> is_lub (x + w) ({x}\<union>A)"
  by (metis join_plus_equiv lub_un)
end

class c_mult_unit =
  fixes c_mult_unit :: "'a" ("u")

class comm_monoid_c_mult = comm_semigroup_c_mult + c_mult_unit + 
  assumes c_mult_unitl [simp]: "u\<parallel>x = x"
begin
lemma c_mult_unitr [simp]: "x\<parallel>u = x"
  by (metis c_mult_comm c_mult_unitl)
end

class ordered_comm_monoid_c_mult = ordered_comm_semigroup_c_mult + comm_monoid_c_mult

class bimonoid = monoid_mult + comm_monoid_c_mult
begin
subclass bisemigroup
  by (unfold_locales)
end

class ordered_bimonoid = ordered_monoid_mult + ordered_comm_monoid_c_mult
begin 
subclass bimonoid
  by (unfold_locales)
end

(***********************************************************************)

section {* Near rings, Semirings and Dioids *}

class near_ring_no_zero = semigroup_mult + ordered_comm_semigroup_add +
  assumes mult_distl [intro]: "x\<cdot>(y+z) = x\<cdot>y+x\<cdot>z"
  and mult_distr [intro]: "(x+y)\<cdot>z = x\<cdot>z+y\<cdot>z" 

class idem_near_ring_no_zero = near_ring_no_zero + idem_comm_semigroup_add
begin
subclass ordered_semigroup_mult
proof 
  fix x y z
  show "x \<le> y \<Longrightarrow> z\<cdot>x \<le> z\<cdot>y"
    by (metis join_plus_equiv leq_def mult_distl)
  show "x \<le> y \<Longrightarrow> x\<cdot>z \<le> y\<cdot>z"
    by (metis join_plus_equiv leq_def mult_distr)
qed
end

class near_ring = near_ring_no_zero + comm_monoid_add +
  assumes mult_annil [simp]: "0\<cdot>x = 0"
  and mult_annir [simp]: "x\<cdot>0 = 0"

class idem_near_ring = idem_comm_monoid_add + near_ring
begin
subclass idem_near_ring_no_zero
  by (unfold_locales)
end

class semiring_mult = near_ring + monoid_mult

class semiring_c_mult = comm_monoid_c_mult + comm_monoid_add +
  assumes c_mult_distl [intro]: "x\<parallel>(y+z) = x\<parallel>y+x\<parallel>z"
  and c_mult_annil [simp]: "0\<parallel>x = 0"
  
begin
lemma c_mult_distr [intro]: "(x+y)\<parallel>z = x\<parallel>z+y\<parallel>z" 
  by (metis c_mult_comm c_mult_distl)

lemma c_mult_annir [simp]: "x\<parallel>0 = 0"
  by (metis c_mult_comm c_mult_annil)
end

class dioid_mult = semiring_mult + idem_semigroup_add
begin
subclass idem_near_ring
  by (unfold_locales)

lemma subdistl: "x\<cdot>z \<le> (x + y)\<cdot>z"
  by (metis join_plus_equiv join_ub mult_isol)

lemma subdistr: "z\<cdot>x \<le> z\<cdot>(x + y)"
  by (metis join_ub join_plus_equiv mult_isor)

lemma mult_double_iso: "w \<le> x \<and> y \<le> z \<longrightarrow> w\<cdot>y \<le> x\<cdot>z"
  by (metis mult_isol mult_isor order_trans)

  primrec power :: "'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<^bsup>_\<^esup>" [101,50] 100) where
    "x\<^bsup>0\<^esup>  = one"
  | "x\<^bsup>Suc n\<^esup> = x\<cdot>x\<^bsup>n\<^esup>"

  lemma power_add: "x\<^bsup>m\<^esup>\<cdot>x\<^bsup>n\<^esup> = x\<^bsup>m+n\<^esup>"
  proof (induct m)
    case 0 show ?case by (metis add_0_left mult_onel power.simps(1))
    case (Suc m) show ?case by (smt Suc add_Suc mult_assoc power.simps(2))
  qed

  lemma power_commutes: "x\<^bsup>n\<^esup>\<cdot>x = x\<cdot>x\<^bsup>n\<^esup>"
    by (smt power_add mult_oner power.simps)

  lemma power_inductl_var: "x\<cdot>y \<le> y \<longrightarrow> (power x n)\<cdot>y \<le> y"
    by (induct n,  metis eq_refl mult_onel power.simps(1), smt add_assoc mult_distl leq_def mult_assoc order_prop power.simps(2) power_commutes)

  lemma power_inductr_var: "y\<cdot>x \<le> y \<longrightarrow> y\<cdot>(power x n) \<le> y"
    by (induct n, metis mult_oner power.simps(1) order_refl, smt add_assoc mult_distr leq_def mult_assoc order_prop power.simps(2)) --"5"

  definition powers :: "'a \<Rightarrow> 'a set" where
    "powers x  = {y. (\<exists>i. y = power x i)}"

  definition powers_c :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
    "powers_c x y z = {x\<cdot>w\<cdot>z| w. (\<exists>i. w = power y i)}"

  lemma powers_c_elim: "v\<in>(powers_c x y z) \<longleftrightarrow> (\<exists>w. v = x\<cdot>w\<cdot>z \<and> (\<exists>i. w = power y i))"
    by (simp add: powers_c_def)

  lemma powers_to_powers_c: "powers x = powers_c one x one"
    by auto (simp add: powers_c_elim mult_onel mult_oner, smt mem_Collect_eq powers_def)+

  lemma power_in_powers_c: "\<forall>i. x\<cdot>(power y i)\<cdot>z \<in> powers_c x y z"
    by (metis powers_c_elim)

  lemma powers_sucl: "powers_c x x one = {y. (\<exists>i. y = power x (Suc i))}"
    by  auto (metis mult_oner powers_c_elim, metis mult_oner power_in_powers_c)

  lemma powers_sucr: "powers_c one x x = {y. (\<exists>i. y = power x (Suc i))}"
    by auto (metis mult_onel power_commutes powers_c_elim, metis mult_onel power_commutes power_in_powers_c)

  lemma powers_suc: "powers_c x x one = powers_c one x x"
    by (metis powers_sucl powers_sucr)

  lemma powers_unfoldl: "{one}\<union>(powers_c x x one) = powers x"
  proof -
    have  "{one}\<union>(powers_c x x one) = {y. y = power x 0 \<or> (\<exists>i. y = power x (Suc i))}"
      by (metis insert_def insert_is_Un power.simps(1) powers_sucl Collect_disj_eq)
    also have "... = {y. (\<exists>i. y = power x i)}"
      by auto (smt power.simps(1), metis power.simps(2), metis (full_types) nat.exhaust power.simps(1) power.simps(2))
    ultimately show ?thesis
      by (metis powers_def)
  qed
end

class dioid_c_mult = semiring_c_mult + idem_comm_monoid_add
begin 
subclass ordered_comm_semigroup_c_mult
proof
  fix x y z
  show "x \<le> y \<Longrightarrow> z\<parallel>x \<le> z\<parallel>y"
    by (metis c_mult_comm c_mult_distr join_plus_equiv leq_def)
qed

lemma c_subdistl: "x\<parallel>z \<le> (x + y)\<parallel>z"
  by (metis join_ub join_plus_equiv c_mult_isol)

lemma c_subdistr: "z\<parallel>x \<le> z\<parallel>(x + y)"
  by (metis join_ub join_plus_equiv c_mult_isor)

lemma mult_double_iso: "w \<le> x \<and> y \<le> z \<longrightarrow> w\<parallel>y \<le> x\<parallel>z"
  by (metis c_mult_isol c_mult_isor order_trans)

end

class bisemiring = semiring_mult + semiring_c_mult

class trioid = dioid_mult + dioid_c_mult
begin 
subclass ordered_bimonoid
  by (unfold_locales)
end

(***********************************************************************)

section {* Quantale *}

class quantale = dioid_mult + complete_lattice + 
  assumes inf_distl: "x \<cdot> \<Sigma> Y = \<Sigma> ((\<lambda>y. x\<cdot>y) ` Y)"
  and inf_distr: "\<Sigma> Y \<cdot> x = \<Sigma> ((\<lambda>y. y\<cdot>x) ` Y)"
begin

lemma bot_zeror: "x \<cdot> \<bottom> = \<bottom>"
  by (metis empty_lub image_empty inf_distl)

lemma bot_zerol: "\<bottom> \<cdot> x = \<bottom>"
  by (metis empty_lub image_empty inf_distr)

lemma mult_left_join_preserving: "join_preserving (\<lambda>y. x\<cdot>y)"
  by (metis inf_distl join_preserving_def)

lemma mult_left_lower: "lower_adjoint (\<lambda>y. x\<cdot>y)"
  by (metis mult_left_join_preserving upper_exists)

lemma mult_right_join_preserving: "join_preserving (\<lambda>y. y\<cdot>x)"
  by (metis inf_distr join_preserving_def)

lemma mult_right_lower: "lower_adjoint (\<lambda>y. y\<cdot>x)"
  by (metis mult_right_join_preserving upper_exists)




end

(***********************************************************************)

section {* Regular Algebra *}

class regular_algebra_right = idem_near_ring + transcl_op +
  assumes transcl_unfoldr [intro]: "x + x\<^sup>+\<cdot>x = x\<^sup>+"
  and transcl_inductr [intro]: "z + y\<cdot>x \<le> y \<Longrightarrow> z\<cdot>x\<^sup>+ \<le> y"
begin

lemma transcl_ext [intro]: "x \<le> x\<^sup>+"
  by (metis add_ub transcl_unfoldr)

end

class regular_algebra = regular_algebra_right +
  assumes transcl_unfoldl [intro]: "x + x\<cdot>x\<^sup>+ = x\<^sup>+"
  and transcl_inductl [intro]: "z + x\<cdot>y \<le> y \<Longrightarrow> x\<^sup>+\<cdot>z \<le> y"


(***********************************************************************)

section {* Kleene Algebra *}
class kleene_algebra = dioid_mult + regular_algebra + star_op + 
  assumes star_def: "x\<^sup>* = 1 + x\<^sup>+"
begin

lemma star_transr: "x\<^sup>+ = x\<^sup>* \<cdot> x"
  by (metis mult_distr mult_onel star_def transcl_unfoldr)

lemma star_transl: "x\<^sup>+ = x \<cdot> x\<^sup>*"
  by (metis mult_distl mult_oner star_def transcl_unfoldl)

lemma one_le_star: "1 \<le> x\<^sup>*"
  by (metis order_prop star_def)

lemma star_1l: "x\<cdot>x\<^sup>* \<le> x\<^sup>*"
  by (metis add_comm join_ub join_plus_equiv mult_distl mult_oner order_trans star_def transcl_unfoldl)

lemma star_1r: "x\<^sup>*\<cdot>x \<le> x\<^sup>*"
  by (metis add_comm join_ub join_plus_equiv mult_distr mult_onel order_trans star_def transcl_unfoldr)

lemma star_unfoldl: "1 + x\<cdot>x\<^sup>* \<le> x\<^sup>*"
  by (metis add_lub one_le_star star_1l)

lemma star_unfoldr: "1 + x\<^sup>*\<cdot>x \<le> x\<^sup>*"
  by (metis add_lub one_le_star star_1r)

lemma star_inductl: "z + x\<cdot>y \<le> y \<longrightarrow> x\<^sup>*\<cdot>z \<le> y"
  by (metis add_comm add_lub join_iso join_plus_equiv leq_def mult_distr mult_onel star_def transcl_inductl)

lemma star_inductr: "z + y\<cdot>x \<le> y \<longrightarrow> z\<cdot>x\<^sup>* \<le> y"
  by (metis add_comm add_lub join_iso join_plus_equiv leq_def mult_distl mult_oner star_def transcl_inductr)

lemma star_trans_eq: "x\<^sup>*\<cdot>x\<^sup>* = x\<^sup>*"
  by (metis add_comm eq_iff leq_def star_1l star_inductl mult_onel star_def subdistl)

lemma star_inductl_var: "x\<cdot>y \<le> y \<longrightarrow> x\<^sup>*\<cdot>y \<le> y"
  by (metis add_comm eq_refl leq_def star_inductl)

lemma star_subdist:  "x\<^sup>* \<le> (x + y)\<^sup>*"
  by (metis join_plus_equiv join_lub mult_distr star_1l one_le_star star_inductl mult_oner)

lemma star_iso: "x \<le> y \<Longrightarrow> x\<^sup>* \<le> y\<^sup>*"
  by (metis leq_def star_subdist)

lemma star_invol: "x\<^sup>* = (x\<^sup>*)\<^sup>*"
  by (metis add_comm leq_def mult_onel mult_oner star_1l star_def star_inductr star_trans_eq subdistr)

lemma star2: "(1 + x)\<^sup>* = x\<^sup>*"
  by (metis add_comm mult_distr leq_def mult_onel mult_oner star_1l star_inductl star_invol one_le_star star_subdist eq_iff)

lemma star_ext: "x \<le> x\<^sup>*"
  by (metis mult_onel order_trans star_1r star_def subdistl)

lemma star_sim1: "x\<cdot>z \<le> z\<cdot>y \<Longrightarrow> x\<^sup>*\<cdot>z \<le> z\<cdot>y\<^sup>*"
proof -
  assume assm: "x\<cdot>z \<le> z\<cdot>y"
  hence "(x\<cdot>z)\<cdot>y\<^sup>* \<le> (z\<cdot>y)\<cdot>y\<^sup>*"
    by (metis assm mult_isol)
  hence "(x\<cdot>z)\<cdot>y\<^sup>* \<le> z\<cdot>y\<^sup>*"
    by (metis mult_assoc mult_isor order_trans star_1l)
  hence "z + (x\<cdot>z)\<cdot>y\<^sup>* \<le> z\<cdot>y\<^sup>*"
    by (metis join_lub join_plus_equiv mult_oner star_def subdistr)
  thus ?thesis
    by (metis mult_assoc star_inductl)
qed

lemma star_sim2: "z\<cdot>x \<le> y\<cdot>z \<Longrightarrow> z\<cdot>x\<^sup>* \<le> y\<^sup>*\<cdot>z"
proof -
  assume assm: "z\<cdot>x \<le> y\<cdot>z"
  hence "y\<^sup>*\<cdot>(z\<cdot>x) \<le> y\<^sup>*\<cdot>(y\<cdot>z)"
    by (metis assm mult_isor)
  hence "y\<^sup>*\<cdot>(z\<cdot>x) \<le> y\<^sup>*\<cdot>z"
    by (metis mult_assoc mult_isol mult_isor order_trans star_ext star_trans_eq)
  hence "z + y\<^sup>*\<cdot>(z\<cdot>x) \<le> y\<^sup>*\<cdot>z"
    by (metis add_lub mult_onel star_def subdistl)
  thus ?thesis
    by (metis mult_assoc star_inductr)
qed

lemma star_slide1: "(x\<cdot>y)\<^sup>*\<cdot>x \<le> x\<cdot>(y\<cdot>x)\<^sup>*"
  by (metis mult_assoc order_refl star_sim1)

lemma star_unfoldl_eq: "x\<^sup>* = 1 + x\<cdot>x\<^sup>*"
  by (smt join_plus_equiv join_comm join_iso mult_distl leq_def_join star_1l one_le_star mult_oner star_inductl antisym star_unfoldl)

lemma star_denest: "(x + y)\<^sup>* = (x\<^sup>*\<cdot>y\<^sup>*)\<^sup>*"
proof -
  have "(x + y)\<^sup>* \<le> (x\<^sup>*\<cdot>y\<^sup>*)\<^sup>*"
    by (metis add_lub mult_double_iso mult_onel mult_oner star_ext star_iso one_le_star)
  thus ?thesis
    by (metis add_comm eq_iff mult_double_iso star_invol star_iso star_subdist star_trans_eq)
qed

lemma star_unfoldr_eq: "1 + x\<^sup>*\<cdot>x = x\<^sup>*"
  by (smt mult_distl mult_distr mult_assoc mult_onel mult_oner star_unfoldl_eq star_inductl eq_iff star_unfoldr)

lemma star_slide: "(x\<cdot>y)\<^sup>*\<cdot>x = x\<cdot>(y\<cdot>x)\<^sup>*"
  by (smt add_comm mult_assoc star_unfoldr_eq star_slide1 mult_isor add_iso mult_isol mult_distl mult_oner mult_distr mult_onel star_unfoldl_eq eq_iff star_slide1)

lemma star_slide_var: "x\<^sup>*\<cdot>x = x\<cdot>x\<^sup>*"
  by (metis mult_onel mult_oner star_slide)
end

end

