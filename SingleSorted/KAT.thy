theory KAT
  imports Algebras 
begin

class KAT = kleene_algebra +
  fixes   test_operator :: "'a \<Rightarrow> 'a" ("t_" [100] 101)
  and     comp_operator :: "'a \<Rightarrow> 'a" ("n_" [90] 91)

  assumes test_mult_idem:   "t x \<cdot> t x = t x"
  and     test_mult:        "t (t x \<cdot> t y) = t y \<cdot> t x" 
  and     test_one:         "t 1 = 1"
  and     test_zero:        "t 0 = 0"

  and     test_mult_comp:   "n x \<cdot> n n x = 0"
  and     test_de_morgan:   "n x + n y = n (n n x \<cdot> n n y)"

  and     test_comp_closed: "t (n x) = n (t x)"
  and     test_double_comp: "t x = n n x"
begin

lemma test_proj: "t t x = t x"
  by (metis test_mult test_mult_idem)

lemma test_mult_comm: "t x \<cdot> t y = t y \<cdot> t x"
  by (metis test_mult test_proj)

lemma test_add_closed: "t (t x + t y) = t x + t y"
  by (metis add_comm test_de_morgan test_double_comp test_mult)

lemma test_add_comp: "n x + n n x = 1"
  by (metis mult_oner test_double_comp test_de_morgan test_mult_comp test_one)

lemma test_add_assoc: "t x + (t y + t z) = (t x + t y) + t z" 
  by (metis add_assoc)

lemma test_add_comm: "t x + t y = t y + t x"
  by (metis add_comm)

lemma test_add_zerol: "0 + t x = t x"
  by (metis add_zerol)

lemma test_add_zeror: "t x + 0 = t x"
  by (metis add_zeror)

lemma test_add_distl: "(t x \<cdot> t y) + t z = (t x + t z) \<cdot> (t y + t z)"
proof -
  have one: "(t x \<cdot> t y) + t z \<le> (t x + t z) \<cdot> (t y + t z)"
    by (metis add_lub mult_double_iso order_refl test_mult_idem)
  have "t x \<cdot> t y + t x \<cdot> t z \<le>  (t x \<cdot> t y) + t z"
    by (metis (mono_tags) add_comm add_iso add_ub mult_isor mult_oner test_add_comp test_double_comp test_mult_comm)
  moreover have "t z \<cdot> t y + t z \<le> (t x \<cdot> t y) + t z"
    by (metis add_comm add_ub leq_def mult_oner subdistr test_add_comp test_double_comp)
  moreover have  "(t x + t z) \<cdot> (t y + t z) = (t x \<cdot> t y + t x \<cdot> t z) + (t z \<cdot> t y + t z)"
    by (metis mult_distr mult_distl test_mult_idem)
  ultimately have two: "(t x + t z) \<cdot> (t y + t z) \<le> (t x \<cdot> t y) + t z"
    by (metis add_lub)
  show ?thesis
    by (metis eq_iff one two)
qed

lemma test_add_distr: "t x + (t y \<cdot> t z) = (t x + t y) \<cdot> (t x + t z)"
  by (metis add_comm test_add_distl)

lemma test_mult_assoc: "t x \<cdot> (t y \<cdot> t z) = (t x \<cdot> t y) \<cdot> t z"
  by (metis mult_assoc)

lemma test_mult_onel: "1 \<cdot> t x = t x"
  by (metis mult_onel)

lemma test_mult_oner: "t x \<cdot> 1 = t x"
  by (metis mult_oner)

lemma test_mult_distl: "t x \<cdot> (t y + t z) = (t x \<cdot> t y) + (t x \<cdot> t z)"
  by (metis mult_distl)

lemma test_mult_distr: "(t x + t y) \<cdot> t z = (t x \<cdot> t z) + (t y \<cdot> t z)"
  by (metis mult_distr)
  
definition test :: "'a \<Rightarrow> bool" where
  "test x \<equiv> t x = x"

lemma test_mult_closed: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> test (x \<cdot> y)"
  by (metis test_def test_mult test_mult_comm)

lemma test_under_one: "test x \<Longrightarrow> x \<le> 1"
  by (metis order_prop test_add_comp test_def test_double_comp)

lemma test_zero_var: "test 0"
  by (metis test_def test_zero)

lemma test_one_var: "test 1"
  by (metis test_def test_one)

lemma test_not_one: "n 1 = 0"
  by (metis mult_oner test_double_comp test_mult_comp test_one)

lemma test_mult_idem_var: "test x \<Longrightarrow> x \<cdot> x = x"
  by (metis test_def test_mult_idem)

lemma test_mult_comm_var: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x \<cdot> y = y \<cdot> x"
  by (metis test_def test_mult_comm)

lemma test_absorb1: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x + x \<cdot> y = x"
  by (metis add_comm leq_def mult_isor mult_oner test_under_one)

lemma test_absorb2: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x \<cdot> (x + y) = x"
  by (metis mult_distl test_absorb1 test_def test_mult_idem)

lemma test_leq_mult_def: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> (x \<le> y) = (x \<cdot> y = x)"
  by (metis add_comm join_plus_equiv leq_def_join test_absorb1 test_absorb2 test_mult_comm_var)

lemma test_double_comp_var: "test x \<Longrightarrow> x = n n x"
  by (metis test_def test_double_comp)

lemma test_comp: "test x \<Longrightarrow> \<exists>y. x + y = 1 \<and> x \<cdot> y = 0"
  by (metis test_add_comp test_def test_double_comp test_mult_comp)

lemma test_comp_uniq: "test x \<Longrightarrow> \<exists>!y. x + y = 1 \<and> x \<cdot> y = 0"
   apply (safe, metis test_comp)
   by (metis add_zerol mult_distl mult_distr mult_onel test_add_comp test_def test_double_comp test_mult_comp)

lemma test_comp_closed_var: "test x \<Longrightarrow> test (n x)"
  by (metis test_comp_closed test_def)

lemma test_add_closed_var: "test x \<and> test y \<Longrightarrow> test (x + y)"
  by (metis test_add_closed test_def)

lemma de_morgan1: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> n x + n y = n (x \<cdot> y)"
  by (metis test_de_morgan test_def test_double_comp)

lemma de_morgan2: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> n x \<cdot> n y = n (x + y)"
  by (smt de_morgan1 test_comp_closed_var test_comp_uniq test_double_comp test_double_comp_var test_mult_closed test_mult_comm_var test_not_one)

lemma test_comp_anti: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> (x \<le> y) = (n y \<le> n x)"
  by (metis add_comm de_morgan1 de_morgan2 join_plus_equiv test_absorb1 test_def test_double_comp test_leq_mult_def)

lemma ba_1: "\<lbrakk>test x; test y; test z\<rbrakk> \<Longrightarrow> x + y + n y = z + n z"
  by (metis add_assoc mult_onel test_absorb1 test_add_comp test_def test_double_comp test_one_var)

lemma ba2: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x + x = x + n (y + n y)"
  by (metis add_idem add_zeror ba_1 test_not_one test_one_var)

lemma ba3: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x = (x \<cdot> y) + (x \<cdot> n y)"
  by (metis mult_distl mult_oner test_add_comp test_def test_double_comp)

lemma ba4: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> x = (x + n y) \<cdot> (x + y)"
proof -
  assume assm: "test x" "test y"
  hence "(x + n y) \<cdot> (x + y) = (x + x \<cdot> y) + (n y \<cdot> x + n y \<cdot> y)"
    by (metis mult_distr mult_distl test_mult_idem_var)
  moreover have "... = x + x \<cdot> y + n y \<cdot> x"
    by (metis add_zeror assm(2) test_double_comp_var test_mult_comp)
  moreover have "... = x"
    by (metis add_assoc add_idem assm mult_distl mult_oner test_add_comp test_def test_double_comp test_mult_comm_var)
  ultimately show ?thesis
    by metis
qed

lemma ba5: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> (x + y) \<cdot> n x = y \<cdot> n x"
  by (metis (hide_lams, no_types) add_comm add_zeror ba4 mult_distr test_comp_closed_var test_comp_uniq test_mult_comm_var test_zero_var)

lemma ba6: "test x \<Longrightarrow> n x \<cdot> x = 0"
  by (metis test_def test_double_comp test_mult_comp)

lemma ba7: "\<lbrakk>test x; test y\<rbrakk> \<Longrightarrow> n x = n (x + y) + n (x + n y)"
  by (metis ba3 de_morgan2 test_comp_closed_var test_double_comp test_double_comp_var)

lemma kat_eq1: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p \<cdot> x \<cdot> n q = 0) = (p \<cdot> x \<le> x \<cdot> q)"
  apply default
  apply (metis add_comm add_zerol ba3 mult_distl mult_isol mult_onel mult_oner test_one_var test_under_one)
  by (metis (hide_lams, no_types) ba6 eq_iff min_zero mult_annir mult_assoc mult_isol test_comp_closed_var test_double_comp_var)

lemma kat_eq2: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p \<cdot> x \<cdot> n q = 0) = (p \<cdot> x = p \<cdot> x \<cdot> q)"
  apply default
  apply (metis add_zerol ba3 mult_distl mult_onel mult_oner test_comp_closed_var test_double_comp_var test_one_var)
  by (metis mult_annir mult_assoc test_def test_double_comp test_mult_comp)

end

end
