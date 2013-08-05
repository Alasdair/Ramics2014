theory FolkTheorem
  imports KAT
begin

context KAT begin

notation comp_operator ("!_" [101] 100)

text {* 
  Kleene algebra star sliding and denesting 
*}
theorem star_sliding: "p\<cdot>(q\<cdot>p)\<^sup>* = (p\<cdot>q)\<^sup>*\<cdot>p"
  by (metis star_slide)

lemma star_denesting1: "(p + q)\<^sup>* \<le> p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>*"
proof -
  have "1 \<le> p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>*"
    by (metis add_lub mult_onel star_def subdistl)
  moreover have "p\<cdot>p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>* \<le> p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>*"
    by (metis mult_isol star_1l)
  moreover have "q\<cdot>p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>* \<le> p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>*"
    by (metis mult_isol mult_onel one_le_star order_trans star_1l)
  moreover have "1 + (p + q)\<cdot>p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>* \<le> 1 + p\<cdot>p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>* + q\<cdot>p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>*"
    by (metis add_assoc mult_distr order_refl)
  ultimately have "... \<le> p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>*"
    by (metis add_lub)
  thus ?thesis
    by (metis add_assoc mult_assoc mult_distr mult_oner star_inductl)
qed

lemma star_denesting2: "p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>* \<le> (p + q)\<^sup>*"
proof -
  have "p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>* \<le> (p + q)\<^sup>*\<cdot>((p + q)\<cdot>(p + q)\<^sup>*)\<^sup>*"
    by (metis add_comm add_ub mult_double_iso star_iso)
  thus ?thesis
    by (metis star2 star_def star_invol star_trans_eq star_transl)
qed

theorem star_denesting: "p\<^sup>*\<cdot>(q\<cdot>p\<^sup>*)\<^sup>* = (p + q)\<^sup>*"
  by (metis add_comm leq_def star_denesting1 star_denesting2)

lemma ka_denesting: "(p\<^sup>* \<cdot> q)\<^sup>* = 1 + (p+q)\<^sup>*\<cdot>q"
  by (metis mult_assoc star_def star_denesting star_slide star_transl)

lemma kat_double: "\<lbrakk>test b; test c\<rbrakk> \<Longrightarrow> b\<cdot>c\<cdot>b\<cdot>p = b\<cdot>c\<cdot>p"
  by (metis (full_types) mult_assoc test_mult_comm_var test_mult_idem_var)

lemma kat_double_zero1: "\<lbrakk>test b; test c\<rbrakk> \<Longrightarrow> b\<cdot>c\<cdot>!b\<cdot>p = 0"
  by (metis mult_annil mult_assoc test_double_comp_var test_mult_comm_var test_mult_comp)

lemma kat_double_zero2: "\<lbrakk>test b; test c\<rbrakk> \<Longrightarrow> !b\<cdot>c\<cdot>b\<cdot>p = 0"
  by (metis kat_double_zero1 test_comp_closed_var test_double_comp_var)


text {* 
  Some commutativity conditions equivalence lemmas 
*}
lemma comm_eq1: "test b \<Longrightarrow> (p\<cdot>b = b\<cdot>p) = (b\<cdot>p\<cdot>!b + !b\<cdot>p\<cdot>b = 0)"
proof (default, metis add_zerol ba6 eq_refl kat_eq1 mult_annil mult_assoc)
  assume tb: "test b" and assm: "b\<cdot>p\<cdot>!b + !b\<cdot>p\<cdot>b = 0"
  have "p\<cdot>b = (b + !b)\<cdot>p\<cdot>b"
    by (metis mult_onel tb test_add_comp test_double_comp_var)
  moreover hence "... = b\<cdot>p\<cdot>b"
    by (metis add_comm add_ub add_zeror assm eq_iff mult_assoc mult_distr)
  moreover have "b\<cdot>p = b\<cdot>p\<cdot>(b + !b)"
    by (metis mult_oner tb test_add_comp test_double_comp_var)
  moreover hence "... = b\<cdot>p\<cdot>b"
    by (metis add_comm add_ub add_zerol assm eq_iff mult_assoc mult_distl)
  ultimately show "p \<cdot> b = b \<cdot> p"
    by (metis)
qed

lemma comm_eq2: "test b \<Longrightarrow> (p\<cdot>!b = !b\<cdot>p) = (b\<cdot>p\<cdot>!b + !b\<cdot>p\<cdot>b = 0)"
  by (metis add_comm comm_eq1 test_comp_closed_var test_double_comp_var)

lemma comm_eq3: "test b \<Longrightarrow> (p\<cdot>b = b\<cdot>p) = (p\<cdot>!b = !b\<cdot>p)"
  by (metis comm_eq1 comm_eq2)

lemma comm_eq4: "\<lbrakk>test b; b\<cdot>q = q\<cdot>b\<rbrakk> \<Longrightarrow> b\<cdot>q\<^sup>* = (b\<cdot>q)\<^sup>*\<cdot>b"
proof - 
  assume tb: "test b" and comm: "b\<cdot>q = q\<cdot>b"
  hence comm2: "b\<cdot>q = b\<cdot>q\<cdot>b"
    by (metis mult_assoc test_mult_idem_var)
  moreover hence "b + (b\<cdot>q)\<^sup>*\<cdot>b\<cdot>q = (1 + (b\<cdot>q)\<^sup>*\<cdot>b\<cdot>q)\<cdot>b"
    by (metis comm mult_assoc mult_distl mult_oner star_def star_sliding star_transr)
  moreover hence "... = (b\<cdot>q)\<^sup>*\<cdot>b"
    by (metis mult_assoc star_def star_transr)
  ultimately have "b\<cdot>q\<^sup>* \<le> (b\<cdot>q)\<^sup>*\<cdot>b"
    by (metis order_refl star_sim2)
  thus ?thesis
    by (metis comm2 eq_iff star_sim1)
qed

lemma comm_eq5: "\<lbrakk>test b; b\<cdot>q = q\<cdot>b\<rbrakk> \<Longrightarrow> b\<cdot>q\<^sup>* = q\<^sup>*\<cdot>b"
  by (metis eq_iff star_sim1 star_sim2)

lemma comm_eq6: "\<lbrakk>test b; b\<cdot>q = q\<cdot>b\<rbrakk> \<Longrightarrow> b\<cdot>q\<^sup>* = b\<cdot>(q\<cdot>b)\<^sup>*"
  by (metis comm_eq4 star_slide)

lemma comm_add: "\<lbrakk>test b; b\<cdot>p = p\<cdot>b; b\<cdot>q = q\<cdot>b\<rbrakk> \<Longrightarrow> b\<cdot>(p + q) = (p + q)\<cdot>b"
  by (metis mult_distl mult_distr)

lemma comm_add_var: "\<lbrakk>test b; test c; test e; b\<cdot>p = p\<cdot>b; b\<cdot>q = q\<cdot>b\<rbrakk> \<Longrightarrow> b\<cdot>(c\<cdot>p + e\<cdot>q) = (c\<cdot>p + e\<cdot>q)\<cdot>b"
  by (metis comm_add mult_assoc test_mult_comm_var)

lemma comm_mult: "\<lbrakk>test b; test c; c\<cdot>p = p\<cdot>c\<rbrakk> \<Longrightarrow> b\<cdot>p\<cdot>c = c\<cdot>b\<cdot>p"
  by (metis mult_assoc test_mult_comm_var)

lemma comm_star: "\<lbrakk>test b; b\<cdot>p = p\<cdot>b; b\<cdot>q = q\<cdot>b\<rbrakk> \<Longrightarrow> b\<cdot>p\<cdot>(b\<cdot>q)\<^sup>* = b\<cdot>p\<cdot>q\<^sup>*"
  by (metis comm_eq4 mult_assoc star_slide)

text {*
  Some distributivity lemmas
*}

lemma folk_distr: "(b + c)\<cdot>(p + q) = b\<cdot>p + c\<cdot>p + b\<cdot>q + c\<cdot>q"
    by (metis add_assoc mult_distl mult_distr)

lemma folk_distr2: 
  assumes tb: "test b" and tc: "test c"
  shows "(b\<cdot>c + !b\<cdot>!c)\<cdot>(b\<cdot>p + !b\<cdot>q) = b\<cdot>c\<cdot>p + !b\<cdot>!c\<cdot>q" 
proof - 
  have "(b\<cdot>c + !b\<cdot>!c)\<cdot>(b\<cdot>p + !b\<cdot>q) = b\<cdot>c\<cdot>b\<cdot>p + !b\<cdot>!c\<cdot>b\<cdot>p + b\<cdot>c\<cdot>!b\<cdot>q + !b\<cdot>!c\<cdot>!b\<cdot>q"
    by (metis folk_distr mult_assoc)
  thus ?thesis
    by (metis tb tc kat_double kat_double_zero1 kat_double_zero2 test_comp_closed_var add_zeror)
qed

lemma folk_de_morgan: "\<lbrakk>test a; test b; test c\<rbrakk> \<Longrightarrow> a\<cdot>b + !a\<cdot>c = (!a + b)\<cdot>(a + c)"
proof -
  assume assm: "test a" "test b" "test c"
  have "(!a + b)\<cdot>(a + c) = b\<cdot>a + !a\<cdot>c + b\<cdot>c"
    by (metis add_assoc mult_distl mult_distr add_zerol assm(1) test_double_comp_var test_mult_comp)
  moreover hence "... = b\<cdot>a + !a\<cdot>c + (a + !a)\<cdot>b\<cdot>c"
    by (metis assm(1) mult_onel test_add_comp test_double_comp_var)
  ultimately have one: "(!a + b)\<cdot>(a + c) = a\<cdot>b + !a\<cdot>c + a\<cdot>b\<cdot>c + !a\<cdot>b\<cdot>c"
    by (metis add_assoc mult_distr assm(1,2) test_mult_comm_var)
  have "a\<cdot>b + !a\<cdot>c = a\<cdot>b\<cdot>(1 + c) + !a\<cdot>c\<cdot>(1 + b)"
    by (metis assm(2,3) mult_assoc mult_distl mult_oner test_absorb1)
  hence two: "a\<cdot>b + !a\<cdot>c = a\<cdot>b + !a\<cdot>c + a\<cdot>b\<cdot>c + !a\<cdot>c\<cdot>b"
    by (metis add_assoc add_comm mult_distl mult_oner)
  from one and two show ?thesis
    by (metis assm(2,3) mult_assoc test_mult_comm_var)
qed

lemma folk_de_morgan2: "\<lbrakk>test a; test b; test c\<rbrakk> \<Longrightarrow> !(a\<cdot>b + !a\<cdot>c) = (a\<cdot>!b + !a\<cdot>!c)"
proof -
  assume assm: "test a" "test b" "test c"
  hence "!(a\<cdot>b + !a\<cdot>c) = !(a\<cdot>b)\<cdot>!(!a\<cdot>c)"
    by (metis de_morgan2 test_comp_closed_var test_mult_closed)
  also have "... = (!a + !b)\<cdot>(a + !c)"
    by (metis assm de_morgan1 test_def test_double_comp)
  finally show ?thesis
    by (metis assm folk_de_morgan test_comp_closed_var)
qed

text {*
  We want to prove that every while program, suitably augmented with finitely many new subprograms 
  of the form s; bc + !b!c, is equivalent to a while program of the form p; while b do q.
  This theorem is proved by induction over the structure of the program.
*}

text {* 
  For the conditional structure, we show that the programs of the form
    s; bc + !b!c
    if b then p1; while d1 do q1
         else p2; while d2 do q2
  are equivalent to
    s; bc + !b!c
    if c then p1 else p2; while cd1 + !cd2 do if c then q1 else q2
*}

lemma conditional_helper1:
  assumes "test b" "test c" "test d" "test e" "test f" "c\<cdot>p = p\<cdot>c" "c\<cdot>q = q\<cdot>c" "c\<cdot>r = r\<cdot>c"
  shows "b\<cdot>c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>*\<cdot>c\<cdot>f = b\<cdot>c\<cdot>p\<cdot>(d\<cdot>q)\<^sup>*\<cdot>f"
proof -
  have "c\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r) = (c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>c"
    by (metis assms(2-4,7,8) comm_add_var test_comp_closed_var test_mult_closed)
  hence "b\<cdot>c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>*\<cdot>c\<cdot>f = b\<cdot>c\<cdot>p\<cdot>c\<cdot>((c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>c)\<^sup>*\<cdot>f"
    by (smt mult_assoc assms(1-4) test_comp_closed_var mult_assoc comm_eq4 comm_eq5)
  also have "... = b\<cdot>c\<cdot>p\<cdot>c\<cdot>(c\<cdot>d\<cdot>q\<cdot>c + !c\<cdot>e\<cdot>r\<cdot>c)\<^sup>*\<cdot>f"
    by (metis mult_distr)
  also have "... = b\<cdot>c\<cdot>p\<cdot>(c\<cdot>c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r\<cdot>c)\<^sup>*\<cdot>f"
    by (metis assms(2-3,6-8) comm_mult mult_assoc test_mult_idem_var)
  also have "... = b\<cdot>c\<cdot>p\<cdot>(c\<cdot>c\<cdot>d\<cdot>q + !c\<cdot>c\<cdot>e\<cdot>r)\<^sup>*\<cdot>f"
    by (metis assms(2,4,8) comm_mult mult_assoc)
  also have "... = b\<cdot>c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q)\<^sup>*\<cdot>f"
    by (metis ba6 assms(2) mult_annil test_mult_idem_var add_zeror)
  finally show ?thesis
    by (smt assms comm_star comm_mult mult_assoc)
qed

lemma conditional_helper2: 
  assumes "test b" "test c" "test d" "test e" "test f" "c\<cdot>p = p\<cdot>c" "c\<cdot>q = q\<cdot>c" "c\<cdot>r = r\<cdot>c"
  shows "b\<cdot>c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>*\<cdot>!c\<cdot>f = 0"
proof -
  have "!c\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r) = (c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>!c"
    by (metis assms(2-4,7,8) comm_add_var comm_eq3 test_comp_closed_var test_mult_closed)
  hence "b\<cdot>c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>*\<cdot>!c\<cdot>f = b\<cdot>c\<cdot>p\<cdot>!c\<cdot>((c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>!c)\<^sup>*\<cdot>f"
    by (smt mult_assoc assms(1-4) test_comp_closed_var mult_assoc comm_eq4 comm_eq5)
  also have "... = b\<cdot>c\<cdot>!c\<cdot>p\<cdot>((c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>!c)\<^sup>*\<cdot>f"
    by (metis assms(2,6) comm_eq3 mult_assoc)
  finally show ?thesis using assms
    by (metis mult_annil mult_assoc test_double_comp_var test_mult_comp)
qed

lemma conditional_helper3:
  assumes "test b" "test c" "test d" "test e" "test f" "c\<cdot>p = p\<cdot>c" "c\<cdot>q = q\<cdot>c" "c\<cdot>r = r\<cdot>c"
  shows "!b\<cdot>!c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>*\<cdot>!c\<cdot>!f = !b\<cdot>!c\<cdot>p\<cdot>(e\<cdot>r)\<^sup>*\<cdot>!f"
proof -
  have comm: "!c\<cdot>p = p\<cdot>!c" "!c\<cdot>q = q\<cdot>!c" "!c\<cdot>r = r\<cdot>!c"
    by (metis assms comm_eq3)+
  have "c\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r) = (c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>c"
    by (metis assms(2-4,7,8) comm_add_var test_comp_closed_var test_mult_closed)
  hence "!b\<cdot>!c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>*\<cdot>!c\<cdot>!f = !b\<cdot>!c\<cdot>p\<cdot>!c\<cdot>((c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>!c)\<^sup>*\<cdot>!f"
    by (smt mult_assoc assms(1-4) test_comp_closed_var mult_assoc comm_eq3 comm_eq4 comm_eq5)
  also have "... = !b\<cdot>!c\<cdot>p\<cdot>!c\<cdot>(c\<cdot>d\<cdot>q\<cdot>!c + !c\<cdot>e\<cdot>r\<cdot>!c)\<^sup>*\<cdot>!f"
    by (metis mult_distr)
  also have "... = !b\<cdot>!c\<cdot>!c\<cdot>p\<cdot>(c\<cdot>!c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r\<cdot>!c)\<^sup>*\<cdot>!f"
    by (metis assms(2,3) comm(1,2) comm_mult mult_assoc test_comp_closed_var)
  also have "... = !b\<cdot>!c\<cdot>!c\<cdot>p\<cdot>(c\<cdot>!c\<cdot>d\<cdot>q + !c\<cdot>!c\<cdot>e\<cdot>r)\<^sup>*\<cdot>!f"
    by (metis assms(2,4) comm(1,3) comm_mult mult_assoc test_comp_closed_var)
  also have "... = !b\<cdot>!c\<cdot>p\<cdot>((c\<cdot>!c)\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>*\<cdot>!f"
    by (metis assms(2) mult_assoc test_comp_closed_var test_mult_idem_var)
  also have "... = !b\<cdot>!c\<cdot>p\<cdot>(!c\<cdot>e\<cdot>r)\<^sup>*\<cdot>!f"
    by (metis assms(2) mult_annil test_double_comp_var test_mult_comp add_zerol)
  finally show ?thesis
    by (smt assms comm comm_star comm_mult mult_assoc test_comp_closed_var)
qed

lemma conditional_helper4: 
  assumes "test b" "test c" "test d" "test e" "test f" "c\<cdot>p = p\<cdot>c" "c\<cdot>q = q\<cdot>c" "c\<cdot>r = r\<cdot>c"
  shows "!b\<cdot>!c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>*\<cdot>c\<cdot>!f = 0"
proof -
  have comm: "!c\<cdot>p = p\<cdot>!c" "!c\<cdot>q = q\<cdot>!c" "!c\<cdot>r = r\<cdot>!c"
    by (metis assms comm_eq3)+
  have "!c\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r) = (c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>!c" using comm_add_var
    by (metis assms(2-4,7,8) comm_eq3 test_comp_closed_var test_mult_closed)
  hence "!b\<cdot>!c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>*\<cdot>c\<cdot>!f = !b\<cdot>!c\<cdot>p\<cdot>c\<cdot>((c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>c)\<^sup>*\<cdot>!f"
    by (smt mult_assoc assms test_comp_closed_var mult_assoc comm_eq3 comm_eq4 comm_eq5)
  also have "... = !b\<cdot>!c\<cdot>c\<cdot>p\<cdot>((c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>c)\<^sup>*\<cdot>!f"
    by (metis assms(2,6) comm_eq3 mult_assoc)
  finally show ?thesis using assms
    by (metis mult_annil mult_assoc test_double_comp_var test_mult_comp)
qed

theorem conditional: 
  assumes "test b" "test c" "test d1" "test d2" "c\<cdot>p1 = p1\<cdot>c" "c\<cdot>p2 = p2\<cdot>c" "c\<cdot>q1 = q1\<cdot>c" "c\<cdot>q2 = q2\<cdot>c"
  shows "(b\<cdot>c + !b\<cdot>!c)\<cdot>(b\<cdot>p1\<cdot>(d1\<cdot>q1)\<^sup>*\<cdot>!d1 + !b\<cdot>p2\<cdot>(d2\<cdot>q2)\<^sup>*\<cdot>!d2) = 
      (b\<cdot>c + !b\<cdot>!c)\<cdot>(c\<cdot>p1 + !c\<cdot>p2)\<cdot>((c\<cdot>d1 + !c\<cdot>d2)\<cdot>(c\<cdot>q1 + !c\<cdot>q2))\<^sup>*\<cdot>!(c\<cdot>d1 + !c\<cdot>d2)"
proof -
  have lhs: "(b\<cdot>c + !b\<cdot>!c)\<cdot>(b\<cdot>p1\<cdot>(d1\<cdot>q1)\<^sup>*\<cdot>!d1 + !b\<cdot>p2\<cdot>(d2\<cdot>q2)\<^sup>*\<cdot>!d2) = b\<cdot>c\<cdot>(p1\<cdot>(d1\<cdot>q1)\<^sup>*\<cdot>!d1) + !b\<cdot>!c\<cdot>(p2\<cdot>(d2\<cdot>q2)\<^sup>*\<cdot>!d2)"
    by (metis assms(1,2) mult_assoc folk_distr2)
  have "(b\<cdot>c + !b\<cdot>!c)\<cdot>(c\<cdot>p1 + !c\<cdot>p2) = b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2"
    by (metis assms(1,2) folk_distr2 test_comp_closed_var test_mult_comm_var)
  moreover have "(c\<cdot>d1 + !c\<cdot>d2)\<cdot>(c\<cdot>q1 + !c\<cdot>q2) = c\<cdot>d1\<cdot>c\<cdot>q1 + c\<cdot>d1\<cdot>!c\<cdot>q2 + !c\<cdot>d2\<cdot>c\<cdot>q1 + !c\<cdot>d2\<cdot>!c\<cdot>q2"
    by (smt add_assoc add_comm mult_distl mult_distr mult_assoc)
  moreover have "... = c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2"
    by (metis assms(2-4) kat_double kat_double_zero1 kat_double_zero2 test_comp_closed_var add_zeror)
  ultimately have one: "(b\<cdot>c + !b\<cdot>!c)\<cdot>(c\<cdot>p1 + !c\<cdot>p2)\<cdot>((c\<cdot>d1 + !c\<cdot>d2)\<cdot>(c\<cdot>q1 + !c\<cdot>q2))\<^sup>*\<cdot>!(c\<cdot>d1 + !c\<cdot>d2)
                  = (b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>(c\<cdot>!d1 + !c\<cdot>!d2)"
    by (metis assms(2-4) folk_de_morgan2)
  hence two: "... = (b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>c\<cdot>!d1 + (b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>!c\<cdot>!d2"
    by (metis mult_assoc mult_distl)
  have "(b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>c\<cdot>!d1 = b\<cdot>c\<cdot>p1\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>c\<cdot>!d1 + !b\<cdot>!c\<cdot>p2\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>c\<cdot>!d1"
    by (metis mult_distr)
  moreover have "... = b\<cdot>c\<cdot>p1\<cdot>(d1\<cdot>q1)\<^sup>*\<cdot>!d1 + !b\<cdot>!c\<cdot>p2\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>c\<cdot>!d1"
    by (metis assms(1-5,7,8) conditional_helper1 test_comp_closed_var)
  ultimately have three: "(b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>c\<cdot>!d1 = b\<cdot>c\<cdot>p1\<cdot>(d1\<cdot>q1)\<^sup>*\<cdot>!d1"
    by (metis assms (1-4,6-8) conditional_helper4 add_zeror)
  have "(b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>!c\<cdot>!d2 = b\<cdot>c\<cdot>p1\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>!c\<cdot>!d2 + !b\<cdot>!c\<cdot>p2\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>!c\<cdot>!d2"
    by (metis mult_distr)
  moreover have "... = !b\<cdot>!c\<cdot>p2\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>!c\<cdot>!d2"
    by (metis assms(1-5,7,8) conditional_helper2 test_comp_closed_var add_zerol)
  ultimately have four: "(b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>*\<cdot>!c\<cdot>!d2 = !b\<cdot>!c\<cdot>p2\<cdot>(d2\<cdot>q2)\<^sup>*\<cdot>!d2"
    by (metis assms(1-4,6-8) conditional_helper3)
  have rhs: "(b\<cdot>c + !b\<cdot>!c)\<cdot>(c\<cdot>p1 + !c\<cdot>p2)\<cdot>((c\<cdot>d1 + !c\<cdot>d2)\<cdot>(c\<cdot>q1 + !c\<cdot>q2))\<^sup>*\<cdot>!(c\<cdot>d1 + !c\<cdot>d2) = b\<cdot>c\<cdot>p1\<cdot>(d1\<cdot>q1)\<^sup>*\<cdot>!d1 + !b\<cdot>!c\<cdot>p2\<cdot>(d2\<cdot>q2)\<^sup>*\<cdot>!d2"
    by (metis one two three four)
  from lhs and rhs show ?thesis
    by (metis mult_assoc)
qed

text {* 
  For nested loops, we show that the programs of the form
    while b do (p; while c do q)
  are equivalent to
    if b then (p; while (b\<or>c) do (if c then q else p)) 
*}

lemma nested_loops_helper: "\<lbrakk>test b; test c\<rbrakk> \<Longrightarrow> (b + c)\<cdot>(c\<cdot>q + !c\<cdot>p) = c\<cdot>q + !c\<cdot>b\<cdot>p"
proof -
  assume assms: "test b" "test c"
  hence "(b + c)\<cdot>(c\<cdot>q + !c\<cdot>p) = b\<cdot>c\<cdot>q + b\<cdot>!c\<cdot>p + c\<cdot>c\<cdot>q + c\<cdot>!c\<cdot>p"
    by (metis add_assoc mult_distl mult_distr mult_assoc)
  also have "... = b\<cdot>c\<cdot>q + b\<cdot>!c\<cdot>p + c\<cdot>q"
    by (metis add_comm add_zerol assms(2) mult_annil test_double_comp_var test_mult_comp test_mult_idem_var)
  also have "... = b\<cdot>c\<cdot>q + c\<cdot>q + !c\<cdot>b\<cdot>p"
    by (metis assms test_comp_closed_var test_mult_comm_var add_assoc add_comm)
  also have "... = (b + 1)\<cdot>c\<cdot>q + !c\<cdot>b\<cdot>p"
    by (metis mult_distr mult_onel)
  finally show ?thesis
    by (metis add_comm assms(1) mult_onel test_absorb1 test_one_var)
qed

theorem nested_loops: 
  assumes "test b" "test c"
  shows "(b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>*\<cdot>!c)\<^sup>*\<cdot>!b = b\<cdot>p\<cdot>((b + c)\<cdot>(c\<cdot>q + !c\<cdot>p))\<^sup>*\<cdot>!(b + c) + !b"
proof -
  have lhs: "b\<cdot>p\<cdot>((b + c)\<cdot>(c\<cdot>q + !c\<cdot>p))\<^sup>*\<cdot>!(b + c) + !b = b\<cdot>p\<cdot>(c\<cdot>q + !c\<cdot>b\<cdot>p)\<^sup>*\<cdot>!b\<cdot>!c + !b"
    by (metis assms nested_loops_helper de_morgan2 mult_assoc)
  have "(b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>*\<cdot>!c)\<^sup>*\<cdot>!b = (1 + b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>*\<cdot>!c\<cdot>(b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>*\<cdot>!c)\<^sup>*)\<cdot>!b"
    by (metis star_unfoldl_eq)
  moreover have "... = !b + b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>*\<cdot>!c\<cdot>(b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>*\<cdot>!c)\<^sup>*\<cdot>!b"
    by (metis mult_distr mult_onel)
  moreover have "... = !b + b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>*\<cdot>(!c\<cdot>b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>*)\<^sup>*\<cdot>!c\<cdot>!b"
    by (metis mult_assoc star_sliding)
  moreover have "(c\<cdot>q + !c\<cdot>b\<cdot>p)\<^sup>* = (c\<cdot>q)\<^sup>*\<cdot>(!c\<cdot>b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>*)\<^sup>*"
    by (metis star_denesting)
  ultimately have rhs: "(b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>*\<cdot>!c)\<^sup>*\<cdot>!b = b\<cdot>p\<cdot>(c\<cdot>q + !c\<cdot>b\<cdot>p)\<^sup>*\<cdot>!b\<cdot>!c + !b"
    by (metis assms test_comp_closed_var test_mult_comm_var mult_assoc add_comm)
  from lhs and rhs show ?thesis
    by metis
qed

text {* 
  For postcomputation, we show that the programs of the form
    while b do p; q
  are equivalent to assuming without loss of generality that b and q commute
    if !b then q else while b do (p; if !b the q)) 
*}
theorem postcomputation: 
  assumes "test b" "p\<cdot>b = b\<cdot>p" "q\<cdot>b = b\<cdot>q" 
  shows "(b\<cdot>p)\<^sup>*\<cdot>!b\<cdot>q = !b\<cdot>q + b\<cdot>(b\<cdot>p\<cdot>(!b\<cdot>q + b))\<^sup>*\<cdot>!b"
proof -
  have lhs: "(b\<cdot>p)\<^sup>*\<cdot>!b\<cdot>q = !b\<cdot>q + b\<cdot>p\<cdot>(b\<cdot>p)\<^sup>*\<cdot>!b\<cdot>q"
    by (metis mult_distr mult_onel star_def star_transl)
  have "b\<cdot>(b\<cdot>p\<cdot>(!b\<cdot>q + b))\<^sup>*\<cdot>!b = b\<cdot>!b + b\<cdot>b\<cdot>p\<cdot>(!b\<cdot>q + b)\<cdot>(b\<cdot>p\<cdot>(!b\<cdot>q + b))\<^sup>*\<cdot>!b"
    by (metis mult_distl mult_distr mult_oner mult_assoc star_unfoldl_eq)
  also have "... = b\<cdot>p\<cdot>(!b\<cdot>q + b)\<cdot>(b\<cdot>p\<cdot>(!b\<cdot>q + b))\<^sup>*\<cdot>!b" 
    by (metis assms(1) ba6 comm_eq3 add_zerol test_mult_idem_var)
  also have "... = b\<cdot>p\<cdot>((!b\<cdot>q + b)\<cdot>b\<cdot>p)\<^sup>*\<cdot>(!b\<cdot>q + b)\<cdot>!b" 
    by (metis mult_assoc star_slide)
  also have "... = b\<cdot>p\<cdot>((!b\<cdot>q\<cdot>b + b\<cdot>b)\<cdot>p)\<^sup>*\<cdot>(!b\<cdot>q\<cdot>!b + b\<cdot>!b)"
    by (metis mult_distr mult_assoc)
  also have "... = b\<cdot>p\<cdot>((!b\<cdot>q\<cdot>b + b)\<cdot>p)\<^sup>*\<cdot>(!b\<cdot>q\<cdot>!b)"
    by (metis assms(1) ba6 comm_eq3 add_zeror test_mult_idem_var)
  also have "... = b\<cdot>p\<cdot>((!b\<cdot>b\<cdot>q + b)\<cdot>p)\<^sup>*\<cdot>(!b\<cdot>!b\<cdot>q)"
    by (metis assms(1,3) comm_eq3 mult_assoc)
  finally have rhs: "b\<cdot>(b\<cdot>p\<cdot>(!b\<cdot>q + b))\<^sup>*\<cdot>!b = b\<cdot>p\<cdot>(b\<cdot>p)\<^sup>*\<cdot>(!b\<cdot>q)"
    by (metis assms(1) ba6 mult_assoc mult_annil add_zerol test_comp_closed_var test_mult_idem_var)
  from lhs and rhs show ?thesis
    by (metis mult_assoc)
qed

text {* 
  For composition, we show that the programs of the form
    while b do p; while c do q
  are equivalent to 
    if !b then while c do q else while b do (p; if !b then while c do q)
*}
theorem composition:
  assumes "test b" "test c" "p\<cdot>b = b\<cdot>p" "q\<cdot>b = b\<cdot>q" 
  shows "(b\<cdot>p)\<^sup>*\<cdot>!b\<cdot>(c\<cdot>q)\<^sup>*\<cdot>!c = !b\<cdot>(c\<cdot>q)\<^sup>*\<cdot>!c + b\<cdot>(b\<cdot>p\<cdot>(!b\<cdot>(c\<cdot>q)\<^sup>*\<cdot>!c + b))\<^sup>*\<cdot>!b"
proof -
  let ?x = "(c\<cdot>q)\<^sup>*\<cdot>!c"
  have "b\<cdot>?x = ?x\<cdot>b"
    by (metis assms(1,2,4) comm_eq5 comm_mult mult_assoc test_comp_closed_var test_mult_comm_var)
  thus ?thesis
    by (metis assms(1,3) mult_assoc postcomputation)
qed

end

end
