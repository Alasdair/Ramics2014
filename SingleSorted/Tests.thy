theory Tests
  imports "$AFP/Kleene_Algebra/Dioid"
begin

text {*
  Tests are embedded in a weak dioid, a dioid without the right annihilation rule, using an 
  operator t defined by a complement operator
*}
class dioid_tests = dioid_one_zerol + 
  fixes   comp_op :: "'a \<Rightarrow> 'a" ("n_" [90] 91)

  assumes test_one:         "n n 1 = 1"
  and     test_zero:        "n n 0 = 0"

  and     test_mult:        "n n (n n x \<cdot> n n y) = n n y \<cdot> n n x" 
  and     test_mult_comp:   "n x \<cdot> n n x = 0"
  and     test_mult_idem:   "n n x \<cdot> n n x = n n x"
  
  and     test_de_morgan:   "n x + n y = n (n n x \<cdot> n n y)"

begin

text {*
  A test operator $t$ can then be defined as an abbreviation of applying $n$ twice.
  The elements of the image, $t(K)$, form a Boolean Algebra.
*}
abbreviation test_operator :: "'a \<Rightarrow> 'a" ("t_" [100] 101) where
  "t x \<equiv> n (n x)"

lemma test_idem: "t t x = t x"
  by (metis add_idem' test_de_morgan test_mult_idem)

lemma test_add_closed: "t (t x + t y) = t x + t y"
  by (metis add_commute test_de_morgan test_mult)

text {* Commutativity laws *}
lemma test_mult_comm: "t x \<cdot> t y = t y \<cdot> t x"
  by (metis test_mult test_idem)

lemma test_add_comm: "t x + t y = t y + t x"
  by (metis add_comm)

text {* Associativity laws *}
lemma test_mult_assoc: "t x \<cdot> (t y \<cdot> t z) = (t x \<cdot> t y) \<cdot> t z"
  by (metis mult_assoc)

lemma test_add_assoc: "t x + (t y + t z) = (t x + t y) + t z" 
  by (metis add_assoc)

text {* Complementation laws *}

lemma test_add_comp: "n x + t x = 1"
  by (metis test_de_morgan test_mult_comp test_one mult_1_left)

lemma "n x \<cdot> t x = 0"
  by (metis test_mult_comp)

text {* Distributivity laws *}

lemma test_distrib_left: "t x \<cdot> (t y + t z) = (t x \<cdot> t y) + (t x \<cdot> t z)"
  by (metis distrib_left)

lemma test_distrib_right: "(t x + t y) \<cdot> t z = (t x \<cdot> t z) + (t y \<cdot> t z)"
  by (metis distrib_right)

lemma test_add_distl: "(t x \<cdot> t y) + t z = (t x + t z) \<cdot> (t y + t z)"
proof -
  have one: "(t x \<cdot> t y) + t z \<le> (t x + t z) \<cdot> (t y + t z)"
    by (smt add_lub add_ub2 distrib_left test_de_morgan test_mult)
  have "t x \<cdot> t y + t x \<cdot> t z \<le>  (t x \<cdot> t y) + t z"
    by (metis add_iso_var order_refl test_mult_comm mult_oner subdistl test_add_comp)
  moreover have "t z \<cdot> t y + t z \<le> (t x \<cdot> t y) + t z"
    by (metis add_comm add_ub1 less_eq_def mult_oner subdistl test_add_comp)
  moreover have  "(t x + t z) \<cdot> (t y + t z) = (t x \<cdot> t y + t x \<cdot> t z) + (t z \<cdot> t y + t z)"
    by (metis distrib_right distrib_left test_mult_idem)
  ultimately have two: "(t x + t z) \<cdot> (t y + t z) \<le> (t x \<cdot> t y) + t z"
    by (metis add_lub)
  show ?thesis
    by (metis eq_iff one two)
qed

lemma test_add_distr: "t x + (t y \<cdot> t z) = (t x + t y) \<cdot> (t x + t z)"
  by (metis add_comm test_add_distl)

text {* Unit laws *}

lemma test_add_zerol: "0 + t x = t x"
  by (metis add_zerol)

lemma test_add_zeror: "t x + 0 = t x"
  by (metis add_zeror)

lemma test_mult_onel: "1 \<cdot> t x = t x"
  by (metis mult_onel)

lemma test_mult_oner: "t x \<cdot> 1 = t x"
  by (metis mult_oner)

text {* Boundaries *}

lemma test_lb: "t x \<ge> 0"
  by (metis zero_least)

lemma test_ub: "t x \<le> 1"
  by (metis add_ub1 test_add_comp)


text {*
  A test is an element $x$ where $t x = x$.
*}  
definition test :: "'a \<Rightarrow> bool" where
  "test x \<equiv> t x = x"

notation comp_op ("!_" [101] 100)

lemma test_add_closed_var: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> test (x + y)"
  by (metis test_add_closed test_def)

lemma test_mult_closed: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> test (x \<cdot> y)"
  by (metis test_def test_mult test_mult_comm)

lemma test_comp_closed: "test x \<Longrightarrow> test (!x)"
  by (metis test_def)

lemma test_ub_var: "test x \<Longrightarrow> x \<le> 1"
  by (metis test_def test_ub)

lemma test_lb_var: "test x \<Longrightarrow> x \<ge> 0"
  by (metis zero_least)

lemma test_zero_var: "test 0"
  by (metis test_def test_zero)

lemma test_one_var: "test 1"
  by (metis test_def test_one)

lemma test_not_one: "!1 = 0"
  by (metis mult_oner test_mult_comp test_one)

lemma test_add_idem: "test x \<Longrightarrow> x + x = x"
  by (metis add_idem')

lemma test_mult_idem_var: "test x \<Longrightarrow> x \<cdot> x = x"
  by (metis test_def test_mult_idem)

lemma test_add_comm_var: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x + y = y + x"
  by (metis add_commute)

lemma test_mult_comm_var: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x \<cdot> y = y \<cdot> x"
  by (metis test_def test_mult_comm)

lemma test_distrib_left_var: "\<lbrakk>test x; test y; test z\<rbrakk> \<Longrightarrow> x\<cdot>(y + z) = x\<cdot>y + x\<cdot>z"
  by (metis distrib_left)

lemma test_distrib_right_var: "\<lbrakk>test x; test y; test z\<rbrakk> \<Longrightarrow> (x + y)\<cdot>z = x\<cdot>z + y\<cdot>z"
  by (metis distrib_right)

lemma test_add_distl_var: "\<lbrakk>test x; test y; test z\<rbrakk> \<Longrightarrow> x\<cdot>y + z = (x + z)\<cdot>(y + z)"
  by (smt test_def test_add_distl)

lemma test_add_distr_var: "\<lbrakk>test x; test y; test z\<rbrakk> \<Longrightarrow> x + y\<cdot>z = (x + y)\<cdot>(x + z)"
  by (metis add_comm test_add_distl_var)

lemma test_absorb1: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x + x \<cdot> y = x"
  by (metis (full_types) add_commute add_ub2 distrib_left less_eq_def test_add_comp test_def test_mult_oner)

lemma test_absorb2: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x \<cdot> (x + y) = x"
  by (metis distrib_left test_mult_idem_var test_absorb1)

lemma test_leq_mult_def: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> (x \<le> y) = (x \<cdot> y = x)"
  by (metis eq_iff test_mult_idem_var mult_1_right mult_isol mult_isor mult_onel test_ub_var)

lemma test_double_comp_var: "test x \<Longrightarrow> x = !(!x)"
  by (metis test_def)

lemma test_comp: "test x \<Longrightarrow> \<exists>y. x + y = 1 \<and> x \<cdot> y = 0"
  by (metis test_add_comp test_def test_mult_comp)

lemma test_comp_uniq: "test x \<Longrightarrow> \<exists>!y. x + y = 1 \<and> x \<cdot> y = 0"
proof (safe, metis test_comp)
  fix y ya assume "test x" "x + ya = x + y" "x \<cdot> ya = x \<cdot> y"
  hence "!x \<cdot> x + !x \<cdot> ya = !x \<cdot> x + !x \<cdot> y"
    by (metis distrib_left)
  hence "!x \<cdot> ya = !x \<cdot> y" using `test x`
    by (metis add_comm add_zeror test_double_comp_var test_mult_comp)
  thus "y = ya" using `x \<cdot> ya = x \<cdot> y` and `test x`
    by (metis distrib_right test_double_comp_var mult_onel test_add_comp)
qed

lemma test_comp_mult: "test x \<Longrightarrow> x \<cdot> !x = 0"
  by (metis test_double_comp_var test_mult_comp)

lemma test_comp_add: "test x \<Longrightarrow> x + !x = 1"
  by (metis test_double_comp_var test_add_comp)

lemma test_comp_closed_var: "test x \<Longrightarrow> test (!x)"
  by (metis test_def)

lemma de_morgan1: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> !x + !y = !(x \<cdot> y)"
  by (metis test_de_morgan test_def)

lemma de_morgan2: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> !x \<cdot> !y = !(x + y)"
  by (smt de_morgan1 test_comp_closed_var test_comp_uniq test_double_comp_var test_mult_closed test_mult_comm_var test_not_one)

lemma test_comp_anti: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> (x \<le> y) = (!y \<le> !x)"
  by (metis add_commute de_morgan1 test_double_comp_var test_mult_closed less_eq_def test_leq_mult_def)

lemma ba_1: "\<lbrakk>test x; test y; test z\<rbrakk> \<Longrightarrow> x + y + !y = z + !z"
  by (metis add_assoc mult_onel test_absorb1 test_add_comp test_def test_one_var)

lemma ba2: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x + x = x + !(y + !y)"
  by (metis add_idem add_zeror ba_1 test_not_one test_one_var)

lemma ba3: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x = (x \<cdot> y) + (x \<cdot> !y)"
  by (metis distrib_left mult_oner test_add_comp test_def)

lemma ba4: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x = (x + !y) \<cdot> (x + y)"
proof -
  assume assm: "test x" "test y"
  hence "(x + !y) \<cdot> (x + y) = (x + x \<cdot> y) + (!y \<cdot> x + !y \<cdot> y)"
    by (metis distrib_right distrib_left test_mult_idem_var)
  moreover have "... = x + x \<cdot> y + !y \<cdot> x"
    by (metis add_zeror assm(2) test_double_comp_var test_mult_comp)
  moreover have "... = x"
    by (metis add_assoc add_idem assm distrib_left mult_oner test_add_comp test_def test_mult_comm_var)
  ultimately show ?thesis
    by metis
qed

lemma ba5: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> (x + y) \<cdot> !x = y \<cdot> !x"
  by (metis (hide_lams, no_types) add_comm add_zeror ba4 distrib_right test_comp_closed_var test_mult_comm_var test_zero_var)

lemma ba6: "test x \<Longrightarrow> !x \<cdot> x = 0"
  by (metis test_def test_mult_comp)

lemma ba7: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> !x = !(x + y) + !(x + !y)"
  by (metis ba3 de_morgan2 test_comp_closed_var test_double_comp_var)


text {*
  Lemmas mixing the embedded tests and any element of the carrier set
*}

lemma test_eq1: "test p \<Longrightarrow> y \<le> x \<longleftrightarrow> p\<cdot>y \<le> x \<and> !p\<cdot>y \<le> x"
  apply default
  apply (metis add_ub1 mult_isol_var test_add_comp mult_isol_var mult_onel test_ub_var)
  by (smt test_comp_add add_assoc add_idem' distrib_right less_eq_def mult_1_left)

lemma test_eq2: "test p \<Longrightarrow> z \<le> p\<cdot>x + !p\<cdot>y \<longleftrightarrow> p\<cdot>z \<le> p\<cdot>x \<and> !p\<cdot>z \<le> !p\<cdot>y"
proof auto
  assume assms: "test p" "z \<le> p\<cdot>x + !p\<cdot>y"
  hence "p\<cdot>(p\<cdot>x + !p\<cdot>y) \<le> p\<cdot>x"
    by (metis mult_isol distrib_left mult_assoc annil test_comp_mult add_lub order_refl test_mult_idem_var zero_least)
  thus "p\<cdot>z \<le> p\<cdot>x"
    by (metis assms(2) mult_isol order_trans)
next
  assume assms: "test p" "z \<le> p\<cdot>x + !p\<cdot>y"
  hence "!p\<cdot>(p\<cdot>x + !p\<cdot>y) \<le> !p\<cdot>y"
    by (metis distrib_left eq_refl mult_assoc annil ba6 add_0_left eq_refl test_def test_mult_idem_var)
  thus "!p\<cdot>z \<le> !p\<cdot>y"
    by (metis assms(2) mult_isol order_trans)
next
  assume assms: "test p" "p\<cdot>z \<le> p\<cdot>x" "!p\<cdot>z \<le> !p\<cdot>y"
  hence "z = p\<cdot>z + !p\<cdot>z"
    by (metis distrib_right mult_onel test_comp_add)
  thus "z \<le> p \<cdot> x + !p \<cdot> y"
    by (metis assms(2,3) add_iso_var)
qed

lemma test_eq3: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q \<longleftrightarrow> p\<cdot>x \<le> x\<cdot>q"
  apply (default, metis mult_isor mult_onel test_ub_var)
  apply (rule antisym, metis mult_assoc mult_isol test_mult_idem_var)
  by (metis mult_isol mult_oner test_ub_var)

lemma test1: "\<lbrakk>test p; test q; p\<cdot>x\<cdot>!q = 0\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  by (metis add_0_left add_commute distrib_left mult_oner test_comp_add)

lemma "\<lbrakk>test p; test q; p\<cdot>x = p\<cdot>x\<cdot>q\<rbrakk> \<Longrightarrow> p\<cdot>x\<cdot>!q = 0"
  nitpick oops

lemma test2: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p\<cdot>q\<cdot>p = p\<cdot>q"
  by (metis eq_refl test_eq3 test_mult_comm_var)

lemma test3: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p\<cdot>q\<cdot>!p = 0"
  by (metis ba5 test_absorb1 test_comp_mult test_mult_closed)

lemma test4: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> !p\<cdot>q\<cdot>p = 0"
  by (metis annil ba6 mult_assoc test_mult_comm_var)

text {* Tests with commutativity conditions *}

lemma comm_add: "\<lbrakk>test b; b\<cdot>p = p\<cdot>b; b\<cdot>q = q\<cdot>b\<rbrakk> \<Longrightarrow> b\<cdot>(p + q) = (p + q)\<cdot>b"
  by (metis distrib_left distrib_right)

lemma comm_add_var: "\<lbrakk>test b; test c; test e; b\<cdot>p = p\<cdot>b; b\<cdot>q = q\<cdot>b\<rbrakk> \<Longrightarrow> b\<cdot>(c\<cdot>p + e\<cdot>q) = (c\<cdot>p + e\<cdot>q)\<cdot>b"
  by (metis comm_add mult_assoc test_mult_comm_var)

lemma comm_mult: "\<lbrakk>test b; test c; c\<cdot>p = p\<cdot>c\<rbrakk> \<Longrightarrow> b\<cdot>p\<cdot>c = c\<cdot>b\<cdot>p"
  by (metis mult_assoc test_mult_comm_var)

lemma de_morgan_var1: "\<lbrakk>test a; test b; test c\<rbrakk> \<Longrightarrow> a\<cdot>b + !a\<cdot>c = (!a + b)\<cdot>(a + c)"
proof -
  assume assm: "test a" "test b" "test c"
  have "(!a + b)\<cdot>(a + c) = !a\<cdot>a + b\<cdot>a + !a\<cdot>c + b\<cdot>c"
    by (metis add_commute combine_common_factor distrib_left distrib_right)
  also have "... = b\<cdot>a + !a\<cdot>c + b\<cdot>c"
    by (metis (full_types) assm(1) add_0_left ba6)
  moreover hence "... = b\<cdot>a + !a\<cdot>c + (a + !a)\<cdot>b\<cdot>c"
    by (metis (full_types) assm(1) calculation(1) test_double_comp_var mult_onel test_add_comp)
  ultimately have one: "(!a + b)\<cdot>(a + c) = a\<cdot>b + !a\<cdot>c + a\<cdot>b\<cdot>c + !a\<cdot>b\<cdot>c"
    by (metis add_assoc distrib_right assm(1,2) test_mult_comm_var)
  have "a\<cdot>b + !a\<cdot>c = a\<cdot>b\<cdot>(1 + c) + !a\<cdot>c\<cdot>(1 + b)"
    by (metis assm(2,3) mult_assoc distrib_left mult_oner test_absorb1)
  hence two: "a\<cdot>b + !a\<cdot>c = a\<cdot>b + !a\<cdot>c + a\<cdot>b\<cdot>c + !a\<cdot>c\<cdot>b"
    by (metis add_assoc add_comm distrib_left mult_oner)
  from one and two show ?thesis
    by (metis assm(2,3) mult_assoc test_mult_comm_var)
qed

lemma de_morgan_var2: "\<lbrakk>test a; test b; test c\<rbrakk> \<Longrightarrow> !(a\<cdot>b + !a\<cdot>c) = (a\<cdot>!b + !a\<cdot>!c)"
proof -
  assume assm: "test a" "test b" "test c"
  hence "!(a\<cdot>b + !a\<cdot>c) = !(a\<cdot>b)\<cdot>!(!a\<cdot>c)"
    by (metis de_morgan2 test_mult_closed test_comp_closed_var)
  also have "... = (!a + !b)\<cdot>(a + !c)"
    by (metis assm de_morgan1 test_def)
  finally show ?thesis
    by (metis assm de_morgan_var1 test_comp_closed_var)
qed

end

end
