theory Lattice
  imports Base
begin

subsection {* Partial orders *}

record 'a ord = "'a partial_object" +
  le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>\<index>" 50)

locale order = fixes A (structure)
  assumes order_refl [intro, simp]: "x \<in> carrier A \<Longrightarrow> x \<sqsubseteq> x"
  and order_trans: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z; x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  and order_antisym: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x = y"

subsubsection {* Order duality *}

definition ord_inv :: "('a, 'b) ord_scheme \<Rightarrow> ('a, 'b) ord_scheme" ("_\<sharp>" [1000] 100) where
  "ord_inv ordr \<equiv> \<lparr>carrier = carrier ordr, le = \<lambda>x y. le ordr y x, \<dots> = ord.more ordr\<rparr>"

lemma inv_carrier_id [simp]: "carrier (ord_inv A) = carrier A"
  by (metis ord_inv_def partial_object.simps(1))

lemma ord_to_inv: "order A \<Longrightarrow> order (ord_inv A)"
  by (default, simp_all add: ord_inv_def, (metis order.order_refl order.order_trans order.order_antisym)+)

lemma inv_inv_id: "ord_inv (A\<sharp>) = A"
  by (simp add: ord_inv_def)

lemma inv_to_ord: "order (A\<sharp>) \<Longrightarrow> order A"
  by (metis inv_inv_id ord_to_inv)

lemma ord_is_inv [simp]: "order (A\<sharp>) = order A"
  by (metis inv_to_ord ord_to_inv)

lemma inv_flip [simp]: "(x \<sqsubseteq>\<^bsub>A\<sharp>\<^esub> y) = (y \<sqsubseteq>\<^bsub>A\<^esub> x)"
  by (simp add: ord_inv_def)

lemma dual_carrier_subset: "X \<subseteq> carrier A \<longleftrightarrow> X \<subseteq> carrier (A\<sharp>)"
  by (metis inv_carrier_id)

subsubsection {* Isotone functions *}

definition isotone :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "isotone A B f \<equiv> order A \<and> order B \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> f y)"

lemma use_iso1: "\<lbrakk>isotone A A f; x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^bsub>A\<^esub> f y"
  by (simp add: isotone_def)

lemma use_iso2: "\<lbrakk>isotone A B f; x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> f y"
  by (simp add: isotone_def)

lemma iso_compose: "\<lbrakk>f \<in> carrier A \<rightarrow> carrier B; isotone A B f; g \<in> carrier B \<rightarrow> carrier C; isotone B C g\<rbrakk> \<Longrightarrow> isotone A C (g \<circ> f)"
  by (simp add: isotone_def, safe, metis (full_types) typed_application)

lemma inv_isotone [simp]: "isotone (A\<sharp>) (B\<sharp>) f = isotone A B f"
  by (simp add: isotone_def, auto)

definition idempotent :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "idempotent A f \<equiv> \<forall>x\<in>A. (f \<circ> f) x = f x"

context order
begin

  lemma eq_refl: "\<lbrakk>x \<in> carrier A; x = x\<rbrakk> \<Longrightarrow> x \<sqsubseteq> x" by (metis order_refl)

  subsection {* Least upper bounds *}

  definition is_ub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_ub x X \<equiv> (X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. y \<sqsubseteq> x)"

  definition is_lub :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_lub x X \<equiv>  is_ub x X \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. z \<sqsubseteq> y) \<longrightarrow> x \<sqsubseteq> y)"

  lemma is_lub_simp: "is_lub x X = ((X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. y \<sqsubseteq> x) \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. z \<sqsubseteq> y) \<longrightarrow> x \<sqsubseteq> y))"
    by (simp add: is_lub_def is_ub_def)

  lemma is_lub_unique: "is_lub x X \<longrightarrow> is_lub y X \<longrightarrow> x = y"
    by (smt order_antisym is_lub_def is_ub_def)

  definition lub :: "'a set \<Rightarrow> 'a" ("\<Sigma>") where
    "\<Sigma> X = (THE x. is_lub x X)"

  lemma lub_simp: "\<Sigma> X = (THE x. (X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. y \<sqsubseteq> x) \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. z \<sqsubseteq> y) \<longrightarrow> x \<sqsubseteq> y))"
    by (simp add: lub_def is_lub_simp)

  lemma the_lub_leq: "\<lbrakk>\<exists>z. is_lub z X; \<And>z. is_lub z X \<longrightarrow> z \<sqsubseteq> x\<rbrakk> \<Longrightarrow> \<Sigma> X \<sqsubseteq> x"
    by (metis is_lub_unique lub_def the_equality)

  lemma the_lub_geq: "\<lbrakk>\<exists>z. is_lub z X; \<And>z. is_lub z X \<Longrightarrow> x \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> \<Sigma> X"
    by (metis is_lub_unique lub_def the_equality)

  lemma lub_is_lub [elim?]: "is_lub w X \<Longrightarrow> \<Sigma> X = w"
    by (metis is_lub_unique lub_def the_equality)

  lemma singleton_lub: "y \<in> carrier A \<Longrightarrow> \<Sigma> {y} = y"
    by (unfold lub_def, rule the_equality, simp_all add: is_lub_def is_ub_def, metis order_antisym order_refl)

  lemma surjective_lub: "\<forall>y\<in>carrier A. \<exists>X\<subseteq>carrier A. y = \<Sigma> X"
    by (metis bot_least insert_subset singleton_lub)

  lemma lub_subset: "\<lbrakk>X \<subseteq> Y; is_lub x X; is_lub y Y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y"
    by (metis (no_types) is_lub_def is_ub_def set_rev_mp)

  lemma lub_closed: "\<lbrakk>X \<subseteq> carrier A; \<exists>x. is_lub x X\<rbrakk> \<Longrightarrow> \<Sigma> X \<in> carrier A"
    by (rule_tac ?P = "\<lambda>x. is_lub x X" in the1I2, metis is_lub_unique, metis is_lub_def is_ub_def lub_is_lub)

  definition join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 70) where
    "x \<squnion> y = \<Sigma> {x,y}"

  subsection {* Greatest lower bounds *}

  definition is_lb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_lb x X \<equiv> (X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. x \<sqsubseteq> y)"

  definition is_glb :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_glb x X \<longleftrightarrow> is_lb x X \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. y \<sqsubseteq> z) \<longrightarrow> y \<sqsubseteq> x)"

  lemma is_glb_simp: "is_glb x X = ((X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. x \<sqsubseteq> y) \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. y \<sqsubseteq> z) \<longrightarrow> y \<sqsubseteq> x))"
     by (simp add: is_glb_def is_lb_def)

  lemma is_glb_unique: "is_glb x X \<longrightarrow> is_glb y X \<longrightarrow> x = y"
    by (smt order_antisym is_glb_def is_lb_def)

  definition glb :: "'a set \<Rightarrow> 'a" ("\<Pi>") where
    "\<Pi> X = (THE x. is_glb x X)"

  lemma glb_simp: "\<Pi> X = (THE x. (X \<subseteq> carrier A) \<and> (x \<in> carrier A) \<and> (\<forall>y\<in>X. x \<sqsubseteq> y) \<and> (\<forall>y\<in>carrier A.(\<forall>z\<in>X. y \<sqsubseteq> z) \<longrightarrow> y \<sqsubseteq> x))"
    by (simp add: glb_def is_glb_simp)

  lemma the_glb_geq: "\<lbrakk>\<exists>z. is_glb z X; \<And>z. is_glb z X \<longrightarrow> x \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> \<Pi> X"
    by (metis glb_def is_glb_unique the_equality)

  lemma the_glb_leq: "\<lbrakk>\<exists>z. is_glb z X; \<And>z. is_glb z X \<longrightarrow> z \<sqsubseteq> x\<rbrakk> \<Longrightarrow> \<Pi> X \<sqsubseteq> x"
    by (metis glb_def is_glb_unique the_equality)

  lemma glb_is_glb [elim?]: "is_glb w X \<Longrightarrow> \<Pi> X = w"
    by (metis is_glb_unique glb_def the_equality)

  lemma singleton_glb: "y \<in> carrier A \<Longrightarrow> \<Pi> {y} = y"
    by (unfold glb_def, rule the_equality, simp_all add: is_glb_def is_lb_def, metis order_antisym order_refl)

  lemma surjective_glb: "\<forall>y\<in>carrier A. \<exists>X\<subseteq>carrier A. y = \<Pi> X"
    by (metis bot_least insert_subset singleton_glb)

  lemma glb_subset: "\<lbrakk>X \<subseteq> Y; is_glb x X; is_glb y Y\<rbrakk> \<Longrightarrow> y \<sqsubseteq> x"
    by (metis (no_types) in_mono is_glb_def is_lb_def)

  lemma glb_closed: "\<lbrakk>X \<subseteq> carrier A; \<exists>x. is_glb x X\<rbrakk> \<Longrightarrow> \<Pi> X \<in> carrier A"
    by (rule_tac ?P = "\<lambda>x. is_glb x X" in the1I2, metis is_glb_unique, metis is_glb_def is_lb_def glb_is_glb)

  definition meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70) where
    "x \<sqinter> y = \<Pi> {x,y}"

  definition less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
    "x \<sqsubset> y \<equiv> (x \<sqsubseteq> y \<and> x \<noteq> y)"

  lemma less_irrefl [iff]: "x \<in> carrier A \<Longrightarrow> \<not> x \<sqsubset> x"
    by (simp add: less_def)

  lemma less_imp_le: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubset> y\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y"
    by (simp add: less_def)

  lemma less_asym: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubset> y; (\<not> P \<Longrightarrow> y \<sqsubset> x)\<rbrakk> \<Longrightarrow> P"
    by (metis order_antisym less_def)

  lemma less_trans: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A; x \<sqsubset> y; y \<sqsubset> z\<rbrakk> \<Longrightarrow> x \<sqsubset> z"
    by (metis less_asym less_def order_trans)

  lemma less_le_trans: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A; x \<sqsubset> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubset> z"
    by (metis less_def less_trans)

  lemma less_asym': "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubset> y; y \<sqsubset> x\<rbrakk> \<Longrightarrow> P"
    by (metis less_asym)

  lemma le_imp_less_or_eq: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> x \<sqsubset> y \<or> x = y"
    by (metis less_def)

  lemma less_imp_not_less: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubset> y\<rbrakk> \<Longrightarrow> (\<not> y \<sqsubset> x) \<longleftrightarrow> True"
    by (metis less_asym)

  lemma less_imp_triv: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubset> y\<rbrakk> \<Longrightarrow> (y \<sqsubset> x \<longrightarrow> P) \<longleftrightarrow> True"
    by (metis less_asym)

  definition is_max :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_max x X \<equiv> x \<in> X \<and> (\<forall>y\<in>X. y \<sqsubseteq> x)"

  definition is_min :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_min x X \<equiv> x \<in> X \<and> (\<forall>y\<in>X. x \<sqsubseteq> y)"

  lemma is_max_equiv: "X \<subseteq> carrier A \<Longrightarrow> is_max x X = (x \<in> X \<and> is_lub x X)"
    by (simp add: is_lub_simp, safe, (metis is_max_def set_mp)+)

  lemma is_min_equiv: "X \<subseteq> carrier A \<Longrightarrow> is_min x X = (x \<in> X \<and> is_glb x X)"
    by (simp add: is_glb_simp, safe, (metis is_min_def set_mp)+)

end

lemma dual_is_max: "order A \<Longrightarrow> order.is_max (A\<sharp>) x X = order.is_min A x X"
  by (simp add: order.is_max_def order.is_min_def)

lemma dual_is_min: "order A \<Longrightarrow> order.is_min (A\<sharp>) x X = order.is_max A x X"
  by (simp add: order.is_max_def order.is_min_def)

abbreviation less_ext :: "'a \<Rightarrow> ('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> bool" ("_\<sqsubset>\<^bsub>_\<^esub>_" [51,0,51] 50) where
  "x \<sqsubset>\<^bsub>A\<^esub> y \<equiv> order.less A x y"

abbreviation lub_ext :: "('a, 'b) ord_scheme \<Rightarrow> 'a set \<Rightarrow> 'a" ("\<Sigma>\<^bsub>_\<^esub>_" [0,1000] 100) where
  "\<Sigma>\<^bsub>A\<^esub>X \<equiv> order.lub A X"

abbreviation glb_ext :: "('a, 'b) ord_scheme \<Rightarrow> 'a set \<Rightarrow> 'a" ("\<Pi>\<^bsub>_\<^esub>_" [0,1000] 100) where
  "\<Pi>\<^bsub>A\<^esub>X \<equiv> order.glb A X"

abbreviation join_ext :: "'a \<Rightarrow> ('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<squnion>\<^bsub>_\<^esub> _" [71,0,70] 70) where
  "x \<squnion>\<^bsub>A\<^esub> y \<equiv> order.join A x y"

abbreviation meet_ext :: "'a \<Rightarrow> ('a, 'b) ord_scheme \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<sqinter>\<^bsub>_\<^esub> _" [70,0,70] 70) where
  "x \<sqinter>\<^bsub>A\<^esub> y \<equiv> order.meet A x y"

subsection {* Join and meet preserving functions *}

definition ex_join_preserving :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "ex_join_preserving A B f \<equiv> order A \<and> order B \<and> (\<forall>X\<subseteq>carrier A. ((\<exists>x\<in>carrier A. order.is_lub A x X) \<longrightarrow> order.lub B (f ` X) = f (order.lub A X)))"

definition ex_meet_preserving :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "ex_meet_preserving A B f \<equiv> order A \<and> order B \<and> (\<forall>X\<subseteq>carrier A. ((\<exists>x\<in>carrier A. order.is_glb A x X) \<longrightarrow> order.glb B (f ` X) = f (order.glb A X)))"

definition join_preserving :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "join_preserving A B f \<equiv> order A \<and> order B \<and> (\<forall>X\<subseteq>carrier A. order.lub B (f ` X) = f (order.lub A X))"

definition meet_preserving :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "meet_preserving A B g \<equiv> order A \<and> order B \<and> (\<forall>X\<subseteq>carrier A. order.glb B (g ` X) = g (order.glb A X))"

lemma dual_is_lub [simp]: "order A \<Longrightarrow> order.is_lub (A\<sharp>) x X = order.is_glb A x X"
  by (simp add: order.is_glb_simp order.is_lub_simp)

lemma dual_is_ub [simp]: "order A \<Longrightarrow> order.is_ub (A\<sharp>) x X = order.is_lb A x X"
  by (simp add: order.is_lb_def order.is_ub_def)

lemma dual_is_glb [simp]: "order A \<Longrightarrow> order.is_glb (A\<sharp>) x X = order.is_lub A x X"
  by (simp add: order.is_glb_simp order.is_lub_simp)

lemma dual_is_lb [simp]: "order A \<Longrightarrow> order.is_lb (A\<sharp>) x X = order.is_ub A x X"
  by (simp add: order.is_lb_def order.is_ub_def)

lemma dual_lub [simp]: "order A \<Longrightarrow> \<Sigma>\<^bsub>A\<sharp>\<^esub>X = \<Pi>\<^bsub>A\<^esub>X"
  by (simp add: order.glb_simp order.lub_simp)

lemma dual_glb [simp]: "order A \<Longrightarrow> \<Pi>\<^bsub>A\<sharp>\<^esub>X = \<Sigma>\<^bsub>A\<^esub>X"
  by (simp add: order.glb_simp order.lub_simp)

lemma common: "\<lbrakk>A \<Longrightarrow> P = Q\<rbrakk> \<Longrightarrow> (A \<and> P) = (A \<and> Q)" by metis

lemma dual_ex_join_preserving [simp]: "ex_join_preserving (A\<sharp>) (B\<sharp>) f = ex_meet_preserving A B f"
  by (simp add: ex_meet_preserving_def ex_join_preserving_def, (rule common)+, simp)

lemma dual_ex_meet_preserving [simp]: "ex_meet_preserving (A\<sharp>) (B\<sharp>) f = ex_join_preserving A B f"
  by (simp add: ex_meet_preserving_def ex_join_preserving_def, (rule common)+, simp)

lemma dual_join_preserving [simp]: "join_preserving (A\<sharp>) (B\<sharp>) f = meet_preserving A B f"
  by (simp add: meet_preserving_def join_preserving_def, (rule common)+, simp)

lemma dual_meet_preserving [simp]: "meet_preserving (A\<sharp>) (B\<sharp>) f = join_preserving A B f"
  by (simp add: meet_preserving_def join_preserving_def, (rule common)+, simp)

hide_fact common

(* +------------------------------------------------------------------------+ *)
subsection {* Join semilattices *}
(* +------------------------------------------------------------------------+ *)

locale join_semilattice = order +
  assumes join_ex: "\<lbrakk>x \<in> carrier A; y\<in>carrier A\<rbrakk> \<Longrightarrow> \<exists>z\<in>carrier A. is_lub z {x,y}"

context join_semilattice
begin

  lemma leq_def: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y) \<longleftrightarrow> (x \<squnion> y = y)"
    apply (simp add: join_def lub_def)
  proof
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and xy: "x \<sqsubseteq> y"
    show "(THE z. is_lub z {x,y}) = y"
      by (rule the_equality, simp_all add: is_lub_def is_ub_def, safe, (metis x_closed y_closed xy order_refl order_antisym)+)
  next
    assume "x \<in> carrier A" and "y \<in> carrier A" and "(THE z. is_lub z {x,y}) = y"
    thus "x \<sqsubseteq> y"
      by (metis insertCI is_lub_def is_ub_def join_ex lub_def lub_is_lub)
  qed

  lemma leq_def_right: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> (x \<squnion> y = y)"
    by (metis leq_def)

  lemma leq_def_left: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; x \<squnion> y = y\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y)"
    by (metis leq_def)

  lemma join_idem: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> x = x" by (metis leq_def order_refl)

  lemma join_comm: "x \<squnion> y = y \<squnion> x" by (metis insert_commute join_def)

  lemma bin_lub_var: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> y \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  proof
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    and join_le_z: "x \<squnion> y \<sqsubseteq> z"
    have "x \<sqsubseteq> z" using join_le_z
      apply (simp add: join_def lub_def)
      apply (rule_tac ?P = "\<lambda>z. is_lub z {x,y}" in the1I2)
      apply (metis join_ex lub_is_lub x_closed y_closed)
      by (smt insertI1 is_lub_def is_ub_def join_def join_le_z lub_is_lub order_trans x_closed z_closed)
    moreover have "y \<sqsubseteq> z" using join_le_z
      apply (simp add: join_def lub_def)
      apply (rule_tac ?P = "\<lambda>z. is_lub z {x,y}" in the1I2)
      apply (metis join_ex lub_is_lub x_closed y_closed)
      by (smt insert_iff is_lub_def is_ub_def join_def join_le_z lub_is_lub order_trans y_closed z_closed)
    ultimately show "x \<sqsubseteq> z \<and> y \<sqsubseteq> z" by auto
  next
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    and xz_and_yz: "x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
    thus "x \<squnion> y \<sqsubseteq> z"
      by (smt emptyE lub_is_lub insertE is_lub_def is_ub_def join_ex join_def ord_le_eq_trans)
  qed

  lemma join_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> y \<in> carrier A"
    by (metis join_def join_ex lub_is_lub)

  lemma join_assoc: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  proof -
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    hence "(x \<squnion> y) \<squnion> z \<sqsubseteq> x \<squnion> (y \<squnion> z)"
      by (metis eq_refl bin_lub_var join_closed)
    thus ?thesis
      by (smt join_closed order_antisym bin_lub_var order_refl x_closed y_closed z_closed)
  qed

end

lemma ex_join_preserving_is_iso:
  assumes f_closed: "f \<in> carrier A \<rightarrow> carrier B"
  and js_A: "join_semilattice A" and js_B: "join_semilattice B"
  and join_pres: "ex_join_preserving A B f"
  shows "isotone A B f"
proof -

  have ord_A: "order A" and ord_B: "order B"
    by (metis ex_join_preserving_def join_pres)+

  have "\<forall>x y. x \<sqsubseteq>\<^bsub>A\<^esub> y \<and> x \<in> carrier A \<and> y \<in> carrier A \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> f y"
  proof clarify
    fix x y assume xy: "x \<sqsubseteq>\<^bsub>A\<^esub> y" and xc: "x \<in> carrier A" and yc: "y \<in> carrier A"

    have xyc: "{x,y} \<subseteq> carrier A"
      by (metis bot_least insert_subset xc yc)

    have ejp: "\<forall>X\<subseteq>carrier A. ((\<exists>x\<in>carrier A. order.is_lub A x X) \<longrightarrow> \<Sigma>\<^bsub>B\<^esub>(f`X) = f (\<Sigma>\<^bsub>A\<^esub>X))"
      by (metis ex_join_preserving_def join_pres)

    have "\<exists>z\<in>carrier A. order.is_lub A z {x,y}"
      by (metis join_semilattice.join_ex js_A xc yc)

    hence xy_join_pres: "f (\<Sigma>\<^bsub>A\<^esub>{x,y}) = \<Sigma>\<^bsub>B\<^esub>{f x, f y}"
      by (metis ejp xyc image_empty image_insert)

    have "f (\<Sigma>\<^bsub>A\<^esub>{x,y}) = f y"
      by (rule_tac f = f in arg_cong, metis ord_A order.join_def join_semilattice.leq_def_right js_A xc xy yc)

    hence "\<Sigma>\<^bsub>B\<^esub>{f x, f y} = f y"
      by (metis xy_join_pres)

    thus "f x \<sqsubseteq>\<^bsub>B\<^esub> f y"
      by (smt join_semilattice.leq_def_left js_B typed_application f_closed xc yc ord_B order.join_def)
  qed

  thus ?thesis by (metis isotone_def ord_A ord_B)
qed

lemma helper: "\<lbrakk>\<And>x. P x \<and> Q x\<rbrakk> \<Longrightarrow> (\<forall>x. P x) \<and> (\<forall>x. Q x)" by fast

(* +------------------------------------------------------------------------+ *)
subsection {* Meet semilattices *}
(* +------------------------------------------------------------------------+ *)

locale meet_semilattice = order +
  assumes meet_ex: "\<lbrakk>x \<in> carrier A; y\<in>carrier A\<rbrakk> \<Longrightarrow> \<exists>z\<in>carrier A. is_glb z {x,y}"

context meet_semilattice
begin

  lemma leq_meet_def: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<sqsubseteq> y) \<longleftrightarrow> (x \<sqinter> y = x)"
    apply (simp add: meet_def glb_def)
  proof
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and xy: "x \<sqsubseteq> y"
    show "(THE z. is_glb z {x,y}) = x"
      by (rule the_equality, simp_all add: is_glb_def is_lb_def, safe, (metis x_closed y_closed xy order_refl order_antisym)+)
  next
    assume "x \<in> carrier A" and "y \<in> carrier A" and "(THE z. is_glb z {x,y}) = x"
    thus "x \<sqsubseteq> y"
      by (metis insertCI is_glb_def is_lb_def meet_ex glb_def glb_is_glb)
  qed

  lemma meet_idem: "\<lbrakk>x \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> x = x" by (metis leq_meet_def order_refl)

  lemma meet_comm: "x \<sqinter> y = y \<sqinter> x" by (metis insert_commute meet_def)

  lemma bin_glb_var: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> z \<sqsubseteq> x \<sqinter> y \<longleftrightarrow> z \<sqsubseteq> x \<and> z \<sqsubseteq> y"
  proof
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    and meet_le_z: "z \<sqsubseteq> x \<sqinter> y"
    have "z \<sqsubseteq> x" using meet_le_z
      apply (simp add: meet_def glb_def)
      apply (rule_tac ?P = "\<lambda>z. is_glb z {x,y}" in the1I2)
      apply (metis meet_ex glb_is_glb x_closed y_closed)
      by (smt insertI1 is_glb_def is_lb_def meet_def meet_le_z glb_is_glb order_trans x_closed z_closed)
    moreover have "z \<sqsubseteq> y" using meet_le_z
      apply (simp add: meet_def glb_def)
      apply (rule_tac ?P = "\<lambda>z. is_glb z {x,y}" in the1I2)
      apply (metis meet_ex glb_is_glb x_closed y_closed)
      by (smt insert_iff is_glb_def is_lb_def meet_def meet_le_z glb_is_glb order_trans y_closed z_closed)
    ultimately show "z \<sqsubseteq> x \<and> z \<sqsubseteq> y" by auto
  next
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    and xz_and_yz: "z \<sqsubseteq> x \<and> z \<sqsubseteq> y"
    thus "z \<sqsubseteq> x \<sqinter> y"
      by (smt emptyE glb_is_glb insertE is_glb_def is_lb_def meet_ex meet_def ord_le_eq_trans)
  qed

  lemma meet_closed: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> y \<in> carrier A"
    by (metis meet_def meet_ex glb_is_glb)

  lemma meet_assoc: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> (x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  proof -
    assume x_closed: "x \<in> carrier A" and y_closed: "y \<in> carrier A" and z_closed: "z \<in> carrier A"
    hence "(x \<sqinter> y) \<sqinter> z \<sqsubseteq> x \<sqinter> (y \<sqinter> z)"
      by (metis eq_refl bin_glb_var meet_closed)
    thus ?thesis
      by (smt meet_closed order_antisym bin_glb_var order_refl x_closed y_closed z_closed)
  qed

end

lemma inv_meet_semilattice_is_join [simp]: "meet_semilattice (A\<sharp>) = join_semilattice A"
  by (simp_all add: meet_semilattice_def join_semilattice_def meet_semilattice_axioms_def join_semilattice_axioms_def, safe, simp_all)

lemma inv_join_semilattice_is_meet [simp]: "join_semilattice (A\<sharp>) = meet_semilattice A"
  by (simp add: meet_semilattice_def join_semilattice_def meet_semilattice_axioms_def join_semilattice_axioms_def, safe, simp_all)

lemma ex_meet_preserving_is_iso:
  assumes f_closed: "f \<in> carrier A \<rightarrow> carrier B"
  and js_A: "meet_semilattice A" and js_B: "meet_semilattice B"
  and join_pres: "ex_meet_preserving A B f"
  shows "isotone A B f"
proof -
  have "isotone (A\<sharp>) (B\<sharp>) f"
    by (rule ex_join_preserving_is_iso, simp_all add: f_closed js_A js_B join_pres)
  thus "isotone A B f" by simp
qed

(* +------------------------------------------------------------------------+ *)
subsection {* Lattices *}
(* +------------------------------------------------------------------------+ *)

locale lattice = join_semilattice + meet_semilattice

begin

  lemma absorb1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> (x \<sqinter> y) = x"
    by (metis join_comm leq_def leq_meet_def meet_assoc meet_closed meet_comm meet_idem)

  lemma absorb2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> (x \<squnion> y) = x"
    by (metis join_assoc join_closed join_comm join_idem leq_def leq_meet_def)

  lemma order_change: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x\<sqinter>y = y \<longleftrightarrow> y\<squnion>x = x"
    by (metis leq_def leq_meet_def meet_comm)

  lemma bin_lub_insert:
    assumes xc: "x \<in> carrier A" and X_subset: "X \<subseteq> carrier A"
    and X_lub: "\<exists>y. is_lub y X"
    shows "\<exists>z. is_lub z (insert x X)"
  proof -
    obtain y where y_lub: "is_lub y X" and yc: "y \<in> carrier A" by (metis X_lub is_lub_simp)
    have "\<exists>z. is_lub z (insert x X)"
    proof (intro exI conjI)
      have "\<Sigma> {x, y} \<in> carrier A"
        by (metis join_closed join_def xc yc)
      thus "is_lub (\<Sigma> {x, y}) (insert x X)"
        apply (simp add: is_lub_simp, safe)
        apply (metis xc)
        apply (metis X_subset set_mp)
        apply (metis bin_lub_var join_def order_refl xc yc)
        apply (metis (full_types) absorb2 bin_glb_var is_lub_simp join_comm join_def set_mp xc y_lub yc)
        by (metis bin_lub_var is_lub_simp join_def xc y_lub)
    qed
    thus "\<exists>z. is_lub z (insert x X)"
      by metis
  qed

  lemma set_induct: "\<lbrakk>X \<subseteq> carrier A; finite X; P {}; \<And>y Y. \<lbrakk>finite Y; y \<notin> Y; y \<in> carrier A; P Y\<rbrakk> \<Longrightarrow> P (insert y Y)\<rbrakk> \<Longrightarrow> P X"
    by (metis (no_types) finite_subset_induct)

  lemma finite_lub_var: "\<lbrakk>(insert x X) \<subseteq> carrier A; finite (insert x X)\<rbrakk> \<Longrightarrow> \<exists>z. is_lub z (insert x X)"
    apply (rule_tac X = X and P = "\<lambda>X. \<exists>z. is_lub z (insert x X)" in set_induct)
    apply (metis insert_subset)
    apply (metis finite_insert)
    apply (metis insert_absorb2 insert_subset join_ex)
    apply (simp add: insert_commute)
    apply (rule bin_lub_insert)
    apply metis
    apply (metis is_lub_simp)
    by metis

  lemma finite_lub: "\<lbrakk>X \<subseteq> carrier A; finite X; X \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>x. is_lub x X"
    by (metis finite.simps finite_lub_var)

end

lemma inv_lattice [simp]: "lattice (A\<sharp>) = lattice A"
  by (simp add: lattice_def, auto)

context lattice
begin

  lemma finite_glb:
    assumes "X \<subseteq> carrier A" and "finite X" and "X \<noteq> {}"
    shows "\<exists>x. is_glb x X"
  proof -
    have ord_Ash: "order (A\<sharp>)"
      by (simp, unfold_locales)

    have "\<exists>x. order.is_lub (A\<sharp>) x X"
      by (rule lattice.finite_lub, simp_all add: assms, unfold_locales)
    thus "\<exists>x. is_glb x X"
      by (insert ord_Ash, simp)
  qed

  lemma finite_lub_carrier:
    assumes A_finite: "finite (carrier A)"
    and A_non_empty: "carrier A \<noteq> {}"
    and X_subset: "X \<subseteq> carrier A"
    shows "\<exists>x. is_lub x X"
  proof (cases "X = {}")
    assume x_empty: "X = {}"
    show "\<exists>x. is_lub x X"
    proof (intro exI)
      show "is_lub (\<Pi> (carrier A)) X"
        by (metis (lifting) A_finite A_non_empty X_subset x_empty ex_in_conv finite_glb glb_is_glb is_glb_simp is_lub_def is_ub_def set_eq_subset)
    qed
  next
    assume "X \<noteq> {}"
    thus "\<exists>x. is_lub x X"
      by (metis A_finite X_subset finite_lub rev_finite_subset)
  qed

  lemma finite_glb_carrier:
    assumes A_finite: "finite (carrier A)"
    and A_non_empty: "carrier A \<noteq> {}"
    and X_subset: "X \<subseteq> carrier A"
    shows "\<exists>x. is_glb x X"
  proof -
    have ord_Ash: "order (A\<sharp>)"
      by (simp, unfold_locales)
    have "\<exists>x. order.is_lub (A\<sharp>) x X"
      by (rule lattice.finite_lub_carrier, simp_all add: assms, unfold_locales)
    thus ?thesis by (insert ord_Ash, simp)
  qed

end

(* +------------------------------------------------------------------------+ *)
subsection {* Distributive Lattices *}
(* +------------------------------------------------------------------------+ *)

locale distributive_lattice = lattice +
  assumes dist1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
  and dist2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A; z \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"

(* +------------------------------------------------------------------------+ *)
subsection {* Bounded Lattices *}
(* +------------------------------------------------------------------------+ *)

locale bounded_lattice = lattice +
  assumes bot_ex: "\<exists>b\<in>carrier A. \<forall>x\<in>carrier A. b \<squnion> x = x"
  and top_ex: "\<exists>t\<in>carrier A. \<forall>x\<in>carrier A. t \<sqinter> x = x"

context bounded_lattice
begin

  definition bot :: "'a" ("\<bottom>") where "\<bottom> \<equiv> THE x. x\<in>carrier A \<and> (\<forall>y\<in>carrier A. x \<sqsubseteq> y)"

  lemma bot_closed: "\<bottom> \<in> carrier A"
    apply (simp add: bot_def)
    apply (rule the1I2)
    apply (metis (no_types) bot_ex leq_def_left order_antisym)
    by auto

  definition top :: "'a" ("\<top>") where "\<top> \<equiv> THE x. x\<in>carrier A \<and> (\<forall>y\<in>carrier A. y \<sqsubseteq> x)"

  lemma top_closed: "\<top> \<in> carrier A"
    apply (simp add: top_def)
    apply (rule the1I2)
    apply (metis (hide_lams, no_types) leq_meet_def meet_comm top_ex)
    by auto

  lemma bot_least: "x \<in> carrier A \<Longrightarrow> \<bottom> \<sqsubseteq> x"
    apply (simp add: bot_def)
    apply (rule the1I2)
    apply (metis (no_types) bot_ex leq_def_left order_antisym)
    by auto

  lemma top_greatest: "x \<in> carrier A \<Longrightarrow> x \<sqsubseteq> \<top>"
    apply (simp add: top_def)
    apply (rule the1I2)
    apply (metis (hide_lams, no_types) leq_meet_def meet_comm top_ex)
    by auto

end

(* +------------------------------------------------------------------------+ *)
subsection {* Complemented Lattices *}
(* +------------------------------------------------------------------------+ *)

locale complemented_lattice = bounded_lattice +
  assumes compl: "x \<in> carrier A \<Longrightarrow> \<exists>y. y \<in> carrier A \<and> x \<squnion> y = \<top> \<and> x \<sqinter> y = \<bottom>"

(* +------------------------------------------------------------------------+ *)
subsection {* Boolean algebra *}
(* +------------------------------------------------------------------------+ *)

locale boolean_algebra = complemented_lattice + distributive_lattice

begin

  lemma compl_uniq:
    assumes xc: "x \<in> carrier A"
    shows "\<exists>!y. y \<in> carrier A \<and> x \<squnion> y = \<top> \<and> x \<sqinter> y = \<bottom>"
    apply safe
    apply (metis assms compl)
    by (metis absorb2 assms dist1 join_comm meet_comm)

  definition complement :: "'a \<Rightarrow> 'a" ("!") where
    "complement x = (THE y. y \<in> carrier A \<and> x \<squnion> y = \<top> \<and> x \<sqinter> y = \<bottom>)"

  lemma complement_closed: assumes xc: "x \<in> carrier A" shows "!x \<in> carrier A"
    by (simp add: complement_def, rule the1I2, rule compl_uniq[OF xc], auto)

(*
  lemma complement1: "x \<in> carrier A \<Longrightarrow> x \<squnion> !x = \<top>" sorry

  lemma complement2: "x \<in> carrier A \<Longrightarrow> x \<sqinter> !x = \<bottom>" sorry

  lemma not_one: "!\<top> = \<bottom>" sorry

  lemma not_zero: "!\<bottom> = \<top>" sorry

  lemma double_compl: "x \<in> carrier A \<Longrightarrow> !(!x) = x" sorry

  lemma de_morgan1: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> !x \<sqinter> !y = !(x \<squnion> y)" sorry

  lemma ba_meet_def: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqinter> y = !(!x \<squnion> !y)" sorry

  lemma de_morgan2: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> !x \<squnion> !y = !(x \<sqinter> y)" sorry

  lemma compl_anti: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longleftrightarrow> !y \<sqsubseteq> !x" sorry

  lemma ba_join_def: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x \<squnion> y = !(!x \<sqinter> !y)" sorry

  lemma ba_3: "\<lbrakk>x \<in> carrier A; y \<in> carrier A\<rbrakk> \<Longrightarrow> x = (x \<sqinter> y) \<squnion> (x \<sqinter> !y)" sorry
*)

end

end
