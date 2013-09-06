theory FolkTheorem
  imports KAT
begin

context kat begin

text {*
  Some distributivity helper lemmas
*}

lemma folk_distr: "(b + c)\<cdot>(p + q) = b\<cdot>p + c\<cdot>p + b\<cdot>q + c\<cdot>q"
    by (metis add_assoc distrib_left distrib_right)

lemma folk_distr2: 
  assumes tb: "test b" and tc: "test c"
  shows "(b\<cdot>c + !b\<cdot>!c)\<cdot>(b\<cdot>p + !b\<cdot>q) = b\<cdot>c\<cdot>p + !b\<cdot>!c\<cdot>q" 
proof - 
  have "(b\<cdot>c + !b\<cdot>!c)\<cdot>(b\<cdot>p + !b\<cdot>q) = b\<cdot>c\<cdot>b\<cdot>p + !b\<cdot>!c\<cdot>b\<cdot>p + b\<cdot>c\<cdot>!b\<cdot>q + !b\<cdot>!c\<cdot>!b\<cdot>q"
    by (metis folk_distr mult_assoc)
  thus ?thesis
    by (metis tb tc test2 test3 test4 annil test_comp_closed_var add_zeror)
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
  shows "b\<cdot>c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>\<star>\<cdot>c\<cdot>f = b\<cdot>c\<cdot>p\<cdot>(d\<cdot>q)\<^sup>\<star>\<cdot>f"
proof -
  have "c\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r) = (c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>c"
    by (metis assms(2-4,7,8) comm_add_var test_comp_closed_var test_mult_closed)
  hence "b\<cdot>c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>\<star>\<cdot>c\<cdot>f = b\<cdot>c\<cdot>p\<cdot>c\<cdot>((c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>c)\<^sup>\<star>\<cdot>f"
    by (smt mult_assoc assms(1-4) test_comp_closed_var mult_assoc star_sim_left star_sim3)
  also have "... = b\<cdot>c\<cdot>p\<cdot>c\<cdot>(c\<cdot>d\<cdot>q\<cdot>c + !c\<cdot>e\<cdot>r\<cdot>c)\<^sup>\<star>\<cdot>f"
    by (metis distrib_right)
  also have "... = b\<cdot>c\<cdot>p\<cdot>(c\<cdot>c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r\<cdot>c)\<^sup>\<star>\<cdot>f"
    by (smt assms(1-3,6,7) comm_mult test_mult_closed test_mult_comm_var test_mult_idem_var)
  also have "... = b\<cdot>c\<cdot>p\<cdot>(c\<cdot>c\<cdot>d\<cdot>q + !c\<cdot>c\<cdot>e\<cdot>r)\<^sup>\<star>\<cdot>f"
    by (metis assms(2,4,8) comm_mult mult_assoc)
  also have "... = b\<cdot>c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q)\<^sup>\<star>\<cdot>f"
    by (metis add_0_left add_commute assms(2) comm_eq1 mult_1_left mult_1_right no_trivial_inverse test_one_var test_mult_idem_var)
  finally show ?thesis
    by (smt assms comm_star comm_mult mult_assoc)
qed

lemma conditional_helper2: 
  assumes "test b" "test c" "test d" "test e" "test f" "c\<cdot>p = p\<cdot>c" "c\<cdot>q = q\<cdot>c" "c\<cdot>r = r\<cdot>c"
  shows "b\<cdot>c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>\<star>\<cdot>!c\<cdot>f = 0"
proof -
  have "!c\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r) = (c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>!c"
    by (metis assms(2-4,7,8) comm_add_var comm_eq3 test_comp_closed_var test_mult_closed)
  hence "b\<cdot>c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>\<star>\<cdot>!c\<cdot>f = b\<cdot>c\<cdot>p\<cdot>!c\<cdot>((c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>!c)\<^sup>\<star>\<cdot>f"
    by (smt mult_assoc assms(1-4) test_comp_closed_var mult_assoc star_sim_right star_sim3)
  also have "... = b\<cdot>c\<cdot>!c\<cdot>p\<cdot>((c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>!c)\<^sup>\<star>\<cdot>f"
    by (metis assms(2,6) comm_eq3 mult_assoc)
  finally show ?thesis using assms
    by (metis add_0_left add_commute assms(2) comm_eq1 mult_1_left mult_1_right no_trivial_inverse test_one_var annil mult_assoc)
qed

lemma conditional_helper3:
  assumes "test b" "test c" "test d" "test e" "test f" "c\<cdot>p = p\<cdot>c" "c\<cdot>q = q\<cdot>c" "c\<cdot>r = r\<cdot>c"
  shows "!b\<cdot>!c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>\<star>\<cdot>!c\<cdot>!f = !b\<cdot>!c\<cdot>p\<cdot>(e\<cdot>r)\<^sup>\<star>\<cdot>!f"
proof -
  have comm: "!c\<cdot>p = p\<cdot>!c" "!c\<cdot>q = q\<cdot>!c" "!c\<cdot>r = r\<cdot>!c"
    by (metis assms comm_eq3)+
  have "c\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r) = (c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>c"
    by (metis assms(2-4,7,8) comm_add_var test_comp_closed_var test_mult_closed)
  hence "!b\<cdot>!c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>\<star>\<cdot>!c\<cdot>!f = !b\<cdot>!c\<cdot>p\<cdot>!c\<cdot>((c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>!c)\<^sup>\<star>\<cdot>!f"
    by (smt mult_assoc assms(1-4) test_comp_closed_var mult_assoc comm_eq3 star_sim_right star_sim3)
  also have "... = !b\<cdot>!c\<cdot>p\<cdot>!c\<cdot>(c\<cdot>d\<cdot>q\<cdot>!c + !c\<cdot>e\<cdot>r\<cdot>!c)\<^sup>\<star>\<cdot>!f"
    by (metis distrib_right)
  also have "... = !b\<cdot>!c\<cdot>!c\<cdot>p\<cdot>(c\<cdot>!c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r\<cdot>!c)\<^sup>\<star>\<cdot>!f"
    by (metis assms(2,3) comm(1,2) comm_mult mult_assoc test_comp_closed_var)
  also have "... = !b\<cdot>!c\<cdot>!c\<cdot>p\<cdot>(c\<cdot>!c\<cdot>d\<cdot>q + !c\<cdot>!c\<cdot>e\<cdot>r)\<^sup>\<star>\<cdot>!f"
    by (metis assms(2,4) comm(1,3) comm_mult mult_assoc test_comp_closed_var)
  also have "... = !b\<cdot>!c\<cdot>p\<cdot>((c\<cdot>!c)\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>\<star>\<cdot>!f"
    by (smt assms(2) test_mult_idem_var mult_assoc test_comp_closed_var)
  also have "... = !b\<cdot>!c\<cdot>p\<cdot>(!c\<cdot>e\<cdot>r)\<^sup>\<star>\<cdot>!f"
    by (smt add_comm assms(2-5) calculation comm comm_mult conditional_helper1 test_double_comp_var test_mult_idem_var mult_assoc test_comp_closed_var)
  finally show ?thesis
    by (smt assms comm comm_star comm_mult mult_assoc test_comp_closed_var)
qed

lemma conditional_helper4: 
  assumes "test b" "test c" "test d" "test e" "test f" "c\<cdot>p = p\<cdot>c" "c\<cdot>q = q\<cdot>c" "c\<cdot>r = r\<cdot>c"
  shows "!b\<cdot>!c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>\<star>\<cdot>c\<cdot>!f = 0"
proof -
  have comm: "!c\<cdot>p = p\<cdot>!c" "!c\<cdot>q = q\<cdot>!c" "!c\<cdot>r = r\<cdot>!c"
    by (metis assms comm_eq3)+
  have "!c\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r) = (c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>!c" using comm_add_var
    by (metis assms(2-4,7,8) comm_eq3 test_comp_closed_var test_mult_closed)
  hence "!b\<cdot>!c\<cdot>p\<cdot>(c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<^sup>\<star>\<cdot>c\<cdot>!f = !b\<cdot>!c\<cdot>p\<cdot>c\<cdot>((c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>c)\<^sup>\<star>\<cdot>!f"
    by (smt mult_assoc assms test_comp_closed_var mult_assoc comm_eq3 star_sim_right star_sim3)
  also have "... = !b\<cdot>!c\<cdot>c\<cdot>p\<cdot>((c\<cdot>d\<cdot>q + !c\<cdot>e\<cdot>r)\<cdot>c)\<^sup>\<star>\<cdot>!f"
    by (metis assms(2,6) comm_eq3 mult_assoc)
  finally show ?thesis using assms
    by (smt add_comm comm(1) comm(2) comm(3) conditional_helper2 test_double_comp_var test_comp_closed_var)

qed

theorem conditional: 
  assumes "test b" "test c" "test d1" "test d2" "c\<cdot>p1 = p1\<cdot>c" "c\<cdot>p2 = p2\<cdot>c" "c\<cdot>q1 = q1\<cdot>c" "c\<cdot>q2 = q2\<cdot>c"
  shows "(b\<cdot>c + !b\<cdot>!c)\<cdot>(b\<cdot>p1\<cdot>(d1\<cdot>q1)\<^sup>\<star>\<cdot>!d1 + !b\<cdot>p2\<cdot>(d2\<cdot>q2)\<^sup>\<star>\<cdot>!d2) = 
      (b\<cdot>c + !b\<cdot>!c)\<cdot>(c\<cdot>p1 + !c\<cdot>p2)\<cdot>((c\<cdot>d1 + !c\<cdot>d2)\<cdot>(c\<cdot>q1 + !c\<cdot>q2))\<^sup>\<star>\<cdot>!(c\<cdot>d1 + !c\<cdot>d2)"
proof -
  have lhs: "(b\<cdot>c + !b\<cdot>!c)\<cdot>(b\<cdot>p1\<cdot>(d1\<cdot>q1)\<^sup>\<star>\<cdot>!d1 + !b\<cdot>p2\<cdot>(d2\<cdot>q2)\<^sup>\<star>\<cdot>!d2) = b\<cdot>c\<cdot>(p1\<cdot>(d1\<cdot>q1)\<^sup>\<star>\<cdot>!d1) + !b\<cdot>!c\<cdot>(p2\<cdot>(d2\<cdot>q2)\<^sup>\<star>\<cdot>!d2)"
    by (metis assms(1,2) mult_assoc folk_distr2)
  have "(b\<cdot>c + !b\<cdot>!c)\<cdot>(c\<cdot>p1 + !c\<cdot>p2) = b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2"
    by (metis assms(1,2) folk_distr2 test_comp_closed_var test_mult_comm_var)
  moreover have "(c\<cdot>d1 + !c\<cdot>d2)\<cdot>(c\<cdot>q1 + !c\<cdot>q2) = c\<cdot>d1\<cdot>c\<cdot>q1 + c\<cdot>d1\<cdot>!c\<cdot>q2 + !c\<cdot>d2\<cdot>c\<cdot>q1 + !c\<cdot>d2\<cdot>!c\<cdot>q2"
    by (smt add_assoc add_comm distrib_left distrib_right mult_assoc)
  moreover have "... = c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2"
    by (metis assms(2-4) test2 test3 test4 annil test_comp_closed_var add_zeror)
  ultimately have one: "(b\<cdot>c + !b\<cdot>!c)\<cdot>(c\<cdot>p1 + !c\<cdot>p2)\<cdot>((c\<cdot>d1 + !c\<cdot>d2)\<cdot>(c\<cdot>q1 + !c\<cdot>q2))\<^sup>\<star>\<cdot>!(c\<cdot>d1 + !c\<cdot>d2)
                  = (b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>(c\<cdot>!d1 + !c\<cdot>!d2)"
    by (metis assms(2-4) de_morgan_var2)
  hence two: "... = (b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>c\<cdot>!d1 + (b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>!c\<cdot>!d2"
    by (metis mult_assoc distrib_left)
  have "(b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>c\<cdot>!d1 = b\<cdot>c\<cdot>p1\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>c\<cdot>!d1 + !b\<cdot>!c\<cdot>p2\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>c\<cdot>!d1"
    by (metis distrib_right)
  moreover have "... = b\<cdot>c\<cdot>p1\<cdot>(d1\<cdot>q1)\<^sup>\<star>\<cdot>!d1 + !b\<cdot>!c\<cdot>p2\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>c\<cdot>!d1"
    by (metis assms(1-5,7,8) conditional_helper1 test_comp_closed_var)
  ultimately have three: "(b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>c\<cdot>!d1 = b\<cdot>c\<cdot>p1\<cdot>(d1\<cdot>q1)\<^sup>\<star>\<cdot>!d1"
    by (metis assms (1-4,6-8) conditional_helper4 add_zeror)
  have "(b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>!c\<cdot>!d2 = b\<cdot>c\<cdot>p1\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>!c\<cdot>!d2 + !b\<cdot>!c\<cdot>p2\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>!c\<cdot>!d2"
    by (metis distrib_right)
  moreover have "... = !b\<cdot>!c\<cdot>p2\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>!c\<cdot>!d2"
    by (metis assms(1-5,7,8) conditional_helper2 test_comp_closed_var add_zerol)
  ultimately have four: "(b\<cdot>c\<cdot>p1 + !b\<cdot>!c\<cdot>p2)\<cdot>(c\<cdot>d1\<cdot>q1 + !c\<cdot>d2\<cdot>q2)\<^sup>\<star>\<cdot>!c\<cdot>!d2 = !b\<cdot>!c\<cdot>p2\<cdot>(d2\<cdot>q2)\<^sup>\<star>\<cdot>!d2"
    by (metis assms(1-4,6-8) conditional_helper3)
  have rhs: "(b\<cdot>c + !b\<cdot>!c)\<cdot>(c\<cdot>p1 + !c\<cdot>p2)\<cdot>((c\<cdot>d1 + !c\<cdot>d2)\<cdot>(c\<cdot>q1 + !c\<cdot>q2))\<^sup>\<star>\<cdot>!(c\<cdot>d1 + !c\<cdot>d2) = b\<cdot>c\<cdot>p1\<cdot>(d1\<cdot>q1)\<^sup>\<star>\<cdot>!d1 + !b\<cdot>!c\<cdot>p2\<cdot>(d2\<cdot>q2)\<^sup>\<star>\<cdot>!d2"
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
    by (metis add_assoc distrib_left distrib_right mult_assoc)
  also have "... = b\<cdot>c\<cdot>q + b\<cdot>!c\<cdot>p + c\<cdot>q"
    by (metis add_0_left add_commute annil assms(2) test_mult_idem_var test_comp_mult)
  also have "... = b\<cdot>c\<cdot>q + c\<cdot>q + !c\<cdot>b\<cdot>p"
    by (metis assms test_comp_closed_var test_mult_comm_var add_assoc add_comm)
  also have "... = (b + 1)\<cdot>c\<cdot>q + !c\<cdot>b\<cdot>p"
    by (metis distrib_right mult_onel)
  finally show ?thesis
    by (metis add_comm assms(1) mult_onel test_absorb1 test_one_var)
qed

theorem nested_loops_with_smt: 
  assumes "test b" "test c"
  shows "(b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>\<star>\<cdot>!c)\<^sup>\<star>\<cdot>!b = b\<cdot>p\<cdot>((b + c)\<cdot>(c\<cdot>q + !c\<cdot>p))\<^sup>\<star>\<cdot>!(b + c) + !b"
  by (smt assms nested_loops_helper de_morgan2 mult_assoc star_unfoldl_eq distrib_right mult_onel mult_assoc star_slide star_denest_var assms test_comp_closed_var test_mult_comm_var mult_assoc add_comm )

theorem nested_loops: 
  assumes "test b" "test c"
  shows "(b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>\<star>\<cdot>!c)\<^sup>\<star>\<cdot>!b = b\<cdot>p\<cdot>((b + c)\<cdot>(c\<cdot>q + !c\<cdot>p))\<^sup>\<star>\<cdot>!(b + c) + !b"
proof -
  have lhs: "b\<cdot>p\<cdot>((b + c)\<cdot>(c\<cdot>q + !c\<cdot>p))\<^sup>\<star>\<cdot>!(b + c) + !b = b\<cdot>p\<cdot>(c\<cdot>q + !c\<cdot>b\<cdot>p)\<^sup>\<star>\<cdot>!b\<cdot>!c + !b"
    by (metis assms nested_loops_helper de_morgan2 mult_assoc)
  have "(b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>\<star>\<cdot>!c)\<^sup>\<star>\<cdot>!b = (1 + b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>\<star>\<cdot>!c\<cdot>(b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>\<star>\<cdot>!c)\<^sup>\<star>)\<cdot>!b"
    by (metis star_unfoldl_eq)
  moreover have "... = !b + b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>\<star>\<cdot>!c\<cdot>(b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>\<star>\<cdot>!c)\<^sup>\<star>\<cdot>!b"
    by (metis distrib_right mult_onel)
  moreover have "... = !b + b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>\<star>\<cdot>(!c\<cdot>b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>\<star>)\<^sup>\<star>\<cdot>!c\<cdot>!b"
    by (metis mult_assoc star_slide)
  moreover have "(c\<cdot>q + !c\<cdot>b\<cdot>p)\<^sup>\<star> = (c\<cdot>q)\<^sup>\<star>\<cdot>(!c\<cdot>b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>\<star>)\<^sup>\<star>"
    by (metis star_denest_var)
  ultimately have rhs: "(b\<cdot>p\<cdot>(c\<cdot>q)\<^sup>\<star>\<cdot>!c)\<^sup>\<star>\<cdot>!b = b\<cdot>p\<cdot>(c\<cdot>q + !c\<cdot>b\<cdot>p)\<^sup>\<star>\<cdot>!b\<cdot>!c + !b"
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
  shows "(b\<cdot>p)\<^sup>\<star>\<cdot>!b\<cdot>q = !b\<cdot>q + b\<cdot>(b\<cdot>p\<cdot>(!b\<cdot>q + b))\<^sup>\<star>\<cdot>!b"
proof -
  have lhs: "(b\<cdot>p)\<^sup>\<star>\<cdot>!b\<cdot>q = !b\<cdot>q + b\<cdot>p\<cdot>(b\<cdot>p)\<^sup>\<star>\<cdot>!b\<cdot>q"
    by (metis add_commute mult_1_left mult_assoc star_invol star_one star_prod_unfold star_slide star_trans_eq troeger)
  have "b\<cdot>(b\<cdot>p\<cdot>(!b\<cdot>q + b))\<^sup>\<star>\<cdot>!b = b\<cdot>!b + b\<cdot>b\<cdot>p\<cdot>(!b\<cdot>q + b)\<cdot>(b\<cdot>p\<cdot>(!b\<cdot>q + b))\<^sup>\<star>\<cdot>!b"
    by (metis distrib_left distrib_right mult_oner mult_assoc star_unfoldl_eq)
  also have "... = b\<cdot>p\<cdot>(!b\<cdot>q + b)\<cdot>(b\<cdot>p\<cdot>(!b\<cdot>q + b))\<^sup>\<star>\<cdot>!b" 
    by (metis add_zerol assms(1) test_comp_mult test_mult_idem_var)
  also have "... = b\<cdot>p\<cdot>((!b\<cdot>q + b)\<cdot>b\<cdot>p)\<^sup>\<star>\<cdot>(!b\<cdot>q + b)\<cdot>!b" 
    by (metis mult_assoc star_slide)
  also have "... = b\<cdot>p\<cdot>((!b\<cdot>q\<cdot>b + b\<cdot>b)\<cdot>p)\<^sup>\<star>\<cdot>(!b\<cdot>q\<cdot>!b + b\<cdot>!b)"
    by (metis distrib_right mult_assoc)
  also have "... = b\<cdot>p\<cdot>((!b\<cdot>q\<cdot>b + b)\<cdot>p)\<^sup>\<star>\<cdot>(!b\<cdot>q\<cdot>!b)"
    by (smt add_0_left add_commute assms(1) test_mult_idem_var test_comp_mult)
  also have "... = b\<cdot>p\<cdot>((!b\<cdot>b\<cdot>q + b)\<cdot>p)\<^sup>\<star>\<cdot>(!b\<cdot>!b\<cdot>q)"
    by (metis assms(1,3) comm_eq3 mult_assoc)
  finally have rhs: "b\<cdot>(b\<cdot>p\<cdot>(!b\<cdot>q + b))\<^sup>\<star>\<cdot>!b = b\<cdot>p\<cdot>(b\<cdot>p)\<^sup>\<star>\<cdot>(!b\<cdot>q)"
    by (metis add_0_right add_commute annil assms(1) ba6 assms(1) test_mult_idem test_def)
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
  shows "(b\<cdot>p)\<^sup>\<star>\<cdot>!b\<cdot>(c\<cdot>q)\<^sup>\<star>\<cdot>!c = !b\<cdot>(c\<cdot>q)\<^sup>\<star>\<cdot>!c + b\<cdot>(b\<cdot>p\<cdot>(!b\<cdot>(c\<cdot>q)\<^sup>\<star>\<cdot>!c + b))\<^sup>\<star>\<cdot>!b"
proof -
  let ?x = "(c\<cdot>q)\<^sup>\<star>\<cdot>!c"
  have "b\<cdot>?x = ?x\<cdot>b"
    by (metis assms(1,2,4) star_sim3 comm_mult mult_assoc test_comp_closed_var test_mult_comm_var)
  thus ?thesis
    by (metis assms(1,3) mult_assoc postcomputation)
qed

end

end
