-- What the user writes:

definition infinite_primes (n : nat) : {p | p ≥ n ∧ prime p} :=
let m := fact (n + 1) in
have m ≥ 1,     from le_of_lt_succ (succ_lt_succ (fact_pos _)),
have m + 1 ≥ 2, from succ_le_succ this,
obtain p `prime p` `p ∣ m + 1`, from sub_prime_and_dvd this,
have p ≥ 2, from ge_two_of_prime `prime p`,
have p > 0, from lt_of_succ_lt (lt_of_succ_le `p ≥ 2`),
have p ≥ n, from by_contradiction
  (suppose ¬ p ≥ n,
    have p < n,     from lt_of_not_ge this,
    have p ≤ n + 1, from le_of_lt (lt.step this),
    have p ∣ m,     from dvd_fact `p > 0` this,
    have p ∣ 1,     from dvd_of_dvd_add_right (!add.comm ▸ `p ∣ m + 1`) this,
    have p ≤ 1,     from le_of_dvd zero_lt_one this,
    show false,     from absurd (le.trans `2 ≤ p` `p ≤ 1`) dec_trivial),
subtype.tag p (and.intro this `prime p`)

-- What the kernel sees:

definition nat.infinite_primes : Π (n : nat),
  @subtype.{1} nat
    (λ (p : nat), and (@ge.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15 p n) (nat.prime p)) :=
λ (n : nat),
  (λ
   (this :
     @ge.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15
       (nat.fact
          (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
             (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
       (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)),
     (λ
      (this :
        @ge.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15
          (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2
             (nat.fact
                (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                   (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
             (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22))
          (@bit0.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2
             (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22))),
        (λ
         (H_obtain_from :
           @subtype.{1} nat
             (λ (p : nat),
                and (nat.prime p)
                  (@dvd.{1} nat nat.nat_has_dvd p
                     (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2
                        (nat.fact
                           (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                              (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
                        (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22))))),
           @subtype.cases_on.{1 1} nat
             (λ (p : nat),
                and (nat.prime p)
                  (@dvd.{1} nat nat.nat_has_dvd p
                     (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2
                        (nat.fact
                           (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                              (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
                        (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22))))
             (λ
              (n_1 :
                @subtype.{1} nat
                  (λ (p : nat),
                     and (nat.prime p)
                       (@dvd.{1} nat nat.nat_has_dvd p
                          (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2
                             (nat.fact
                                (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                                   (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
                             (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22))))),
                @subtype.{1} nat
                  (λ (p : nat),
                     and (@ge.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15 p n) (nat.prime p)))
             H_obtain_from
             (λ (p : nat)
              (has_property :
                (λ (p : nat),
                   and (nat.prime p)
                     (@dvd.{1} nat nat.nat_has_dvd p
                        (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2
                           (nat.fact
                              (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                                 (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
                           (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22))))
                  p),
                @and.cases_on.{1} (nat.prime p)
                  (@dvd.{1} nat nat.nat_has_dvd p
                     (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2
                        (nat.fact
                           (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                              (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
                        (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
                  (@subtype.{1} nat
                     (λ (p : nat),
                        and (@ge.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15 p n) (nat.prime p)))
                  has_property
                  (λ (x : nat.prime p)
                   (x_1 :
                     @dvd.{1} nat nat.nat_has_dvd p
                       (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2
                          (nat.fact
                             (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                                (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
                          (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22))),
                     (λ
                      (this :
                        @ge.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15 p
                          (@bit0.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2
                             (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22))),
                        (λ
                         (this_1 :
                           @gt.{1} nat nat._trans_of_decidable_linear_ordered_semiring_13 p
                             (@zero.{1} nat nat._trans_of_decidable_linear_ordered_semiring_6)),
                           (λ (this : @ge.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15 p n),
                              @subtype.tag.{1} nat
                                (λ (p : nat),
                                   and (@ge.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15 p n)
                                     (nat.prime p))
                                p
                                (@and.intro (@ge.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15 p n)
                                   (nat.prime p)
                                   this
                                   x))
                             (@decidable.by_contradiction
                                (@ge.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15 p n)
                                (nat.decidable_le n p)
                                (λ (this_2 : not (@ge.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15 p n)),
                                   (λ (this_2 : @lt.{1} nat nat._trans_of_decidable_linear_ordered_semiring_13 p n),
                                      (λ
                                       (this_2 :
                                         @le.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15 p
                                           (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                                              (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22))),
                                         (λ
                                          (this_1 :
                                            @dvd.{1} nat nat.nat_has_dvd p
                                              (nat.fact
                                                 (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                                                    (@one.{1} nat
                                                       nat._trans_of_decidable_linear_ordered_semiring_22)))),
                                            (λ
                                             (this_1 :
                                               @dvd.{1} nat nat.nat_has_dvd p
                                                 (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)),
                                               (λ
                                                (this_1 :
                                                  @le.{1} nat nat._trans_of_decidable_linear_ordered_semiring_15 p
                                                    (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)),
                                                  (λ (this : false), this)
                                                    (@absurd.{0}
                                                       (@le.{1} nat
                                                          (@weak_order.to_has_le.{1} nat
                                                             nat._trans_of_decidable_linear_ordered_semiring_16)
                                                          (@bit0.{1} nat
                                                             nat._trans_of_decidable_linear_ordered_semiring_2
                                                             (@one.{1} nat
                                                                nat._trans_of_decidable_linear_ordered_semiring_22))
                                                          (@one.{1} nat
                                                             nat._trans_of_decidable_linear_ordered_semiring_22))
                                                       false
                                                       (@le.trans.{1} nat
                                                          nat._trans_of_decidable_linear_ordered_semiring_16
                                                          (@bit0.{1} nat
                                                             nat._trans_of_decidable_linear_ordered_semiring_2
                                                             (@one.{1} nat
                                                                nat._trans_of_decidable_linear_ordered_semiring_22))
                                                          p
                                                          (@one.{1} nat
                                                             nat._trans_of_decidable_linear_ordered_semiring_22)
                                                          this
                                                          this_1)
                                                       (@of_is_true
                                                          (not
                                                             (@le.{1} nat
                                                                (@weak_order.to_has_le.{1} nat
                                                                   nat._trans_of_decidable_linear_ordered_semiring_16)
                                                                (@bit0.{1} nat
                                                                   nat._trans_of_decidable_linear_ordered_semiring_2
                                                                   (@one.{1} nat
                                                                      nat._trans_of_decidable_linear_ordered_semiring_22))
                                                                (@one.{1} nat
                                                                   nat._trans_of_decidable_linear_ordered_semiring_22)))
                                                          (@decidable_not
                                                             (@le.{1} nat
                                                                (@weak_order.to_has_le.{1} nat
                                                                   nat._trans_of_decidable_linear_ordered_semiring_16)
                                                                (@bit0.{1} nat
                                                                   nat._trans_of_decidable_linear_ordered_semiring_2
                                                                   (@one.{1} nat
                                                                      nat._trans_of_decidable_linear_ordered_semiring_22))
                                                                (@one.{1} nat
                                                                   nat._trans_of_decidable_linear_ordered_semiring_22))
                                                             (nat.decidable_le
                                                                (@bit0.{1} nat
                                                                   nat._trans_of_decidable_linear_ordered_semiring_2
                                                                   (@one.{1} nat
                                                                      nat._trans_of_decidable_linear_ordered_semiring_22))
                                                                (@one.{1} nat
                                                                   nat._trans_of_decidable_linear_ordered_semiring_22)))
                                                          trivial)))
                                                 (@nat.le_of_dvd p
                                                    (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)
                                                    (@zero_lt_one.{1} nat
                                                       nat._trans_of_decidable_linear_ordered_semiring_28)
                                                    this_1))
                                              (@nat.dvd_of_dvd_add_right p
                                                 (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)
                                                 (nat.fact
                                                    (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                                                       (@one.{1} nat
                                                          nat._trans_of_decidable_linear_ordered_semiring_22)))
                                                 (@eq.subst.{1} nat
                                                    (@add.{1} nat
                                                       (@add_comm_semigroup._trans_of_to_add_semigroup.{1} nat
                                                          nat._trans_of_decidable_linear_ordered_semiring_7)
                                                       (nat.fact
                                                          (@add.{1} nat
                                                             nat._trans_of_decidable_linear_ordered_semiring_2
                                                             n
                                                             (@one.{1} nat
                                                                nat._trans_of_decidable_linear_ordered_semiring_22)))
                                                       (@one.{1} nat
                                                          nat._trans_of_decidable_linear_ordered_semiring_22))
                                                    (@add.{1} nat
                                                       (@add_comm_semigroup._trans_of_to_add_semigroup.{1} nat
                                                          nat._trans_of_decidable_linear_ordered_semiring_7)
                                                       (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)
                                                       (nat.fact
                                                          (@add.{1} nat
                                                             nat._trans_of_decidable_linear_ordered_semiring_2
                                                             n
                                                             (@one.{1} nat
                                                                nat._trans_of_decidable_linear_ordered_semiring_22))))
                                                    (@dvd.{1} nat nat.nat_has_dvd p)
                                                    (@add.comm.{1} nat nat._trans_of_decidable_linear_ordered_semiring_7
                                                       (nat.fact
                                                          (@add.{1} nat
                                                             nat._trans_of_decidable_linear_ordered_semiring_2
                                                             n
                                                             (@one.{1} nat
                                                                nat._trans_of_decidable_linear_ordered_semiring_22)))
                                                       (@one.{1} nat
                                                          nat._trans_of_decidable_linear_ordered_semiring_22))
                                                    x_1)
                                                 this_1))
                                           (@nat.dvd_fact p
                                              (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                                                 (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22))
                                              this_1
                                              this_2))
                                        (@le_of_lt.{1} nat nat._trans_of_decidable_linear_ordered_semiring_12 p
                                           (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                                              (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22))
                                           (@nat.lt.step p
                                              (@nat.rec.{1} (λ (a : nat), nat) n (λ (b₁ : nat), nat.succ) nat.zero)
                                              this_2)))
                                     (@lt_of_not_ge.{1} nat nat._trans_of_decidable_linear_ordered_semiring_18 p n
                                        this_2))))
                          (@nat.lt_of_succ_lt (@zero.{1} nat nat._trans_of_decidable_linear_ordered_semiring_6) p
                             (@nat.lt_of_succ_le
                                (nat.succ (@zero.{1} nat nat._trans_of_decidable_linear_ordered_semiring_6))
                                p
                                this)))
                       (@nat.ge_two_of_prime p x))))
          (@nat.sub_prime_and_dvd
             (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2
                (nat.fact
                   (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                      (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
                (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22))
             this))
       (@nat.succ_le_succ
          (@nat.rec.{1} (λ (a : nat), nat) (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)
             (λ (b₁ : nat), nat.succ)
             nat.zero)
          (@nat.rec.{1} (λ (a : nat), nat)
             (nat.fact
                (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                   (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
             (λ (b₁ : nat), nat.succ)
             nat.zero)
          this))
    (@nat.le_of_lt_succ (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)
       (nat.fact
          (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
             (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
       (@nat.succ_lt_succ nat.zero
          (nat.fact
             (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))
          (nat.fact_pos
             (@add.{1} nat nat._trans_of_decidable_linear_ordered_semiring_2 n
                (@one.{1} nat nat._trans_of_decidable_linear_ordered_semiring_22)))))
