module

public import Erdos415
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxHeartbeats 0

set_option maxRecDepth 100000

/-!
# A kernel-checked totient table for Erdős Problem 415

The table contains the totients of 0 through 826. Each value is proved by the
prime-factor recurrence for Euler’s totient. The lookup theorem follows from
a single equality between the table and the mapped list of totients.
-/

namespace Erdos415.Certificate

theorem phi_0 : Nat.totient 0 = 0 := Nat.totient_zero

theorem phi_1 : Nat.totient 1 = 1 := Nat.totient_one

theorem phi_2 : Nat.totient 2 = 1 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_3 : Nat.totient 3 = 2 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_4 : Nat.totient 4 = 2 := by
  rw [show 4 = 2 * 2 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_2]
  try norm_num

theorem phi_5 : Nat.totient 5 = 4 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_6 : Nat.totient 6 = 2 := by
  rw [show 6 = 2 * 3 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_3]
  try norm_num

theorem phi_7 : Nat.totient 7 = 6 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_8 : Nat.totient 8 = 4 := by
  rw [show 8 = 2 * 4 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_4]
  try norm_num

theorem phi_9 : Nat.totient 9 = 6 := by
  rw [show 9 = 3 * 3 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_3]
  try norm_num

theorem phi_10 : Nat.totient 10 = 4 := by
  rw [show 10 = 2 * 5 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_5]
  try norm_num

theorem phi_11 : Nat.totient 11 = 10 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_12 : Nat.totient 12 = 4 := by
  rw [show 12 = 2 * 6 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_6]
  try norm_num

theorem phi_13 : Nat.totient 13 = 12 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_14 : Nat.totient 14 = 6 := by
  rw [show 14 = 2 * 7 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_7]
  try norm_num

theorem phi_15 : Nat.totient 15 = 8 := by
  rw [show 15 = 3 * 5 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_5]
  try norm_num

theorem phi_16 : Nat.totient 16 = 8 := by
  rw [show 16 = 2 * 8 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_8]
  try norm_num

theorem phi_17 : Nat.totient 17 = 16 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_18 : Nat.totient 18 = 6 := by
  rw [show 18 = 2 * 9 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_9]
  try norm_num

theorem phi_19 : Nat.totient 19 = 18 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_20 : Nat.totient 20 = 8 := by
  rw [show 20 = 2 * 10 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_10]
  try norm_num

theorem phi_21 : Nat.totient 21 = 12 := by
  rw [show 21 = 3 * 7 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_7]
  try norm_num

theorem phi_22 : Nat.totient 22 = 10 := by
  rw [show 22 = 2 * 11 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_11]
  try norm_num

theorem phi_23 : Nat.totient 23 = 22 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_24 : Nat.totient 24 = 8 := by
  rw [show 24 = 2 * 12 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_12]
  try norm_num

theorem phi_25 : Nat.totient 25 = 20 := by
  rw [show 25 = 5 * 5 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_5]
  try norm_num

theorem phi_26 : Nat.totient 26 = 12 := by
  rw [show 26 = 2 * 13 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_13]
  try norm_num

theorem phi_27 : Nat.totient 27 = 18 := by
  rw [show 27 = 3 * 9 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_9]
  try norm_num

theorem phi_28 : Nat.totient 28 = 12 := by
  rw [show 28 = 2 * 14 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_14]
  try norm_num

theorem phi_29 : Nat.totient 29 = 28 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_30 : Nat.totient 30 = 8 := by
  rw [show 30 = 2 * 15 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_15]
  try norm_num

theorem phi_31 : Nat.totient 31 = 30 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_32 : Nat.totient 32 = 16 := by
  rw [show 32 = 2 * 16 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_16]
  try norm_num

theorem phi_33 : Nat.totient 33 = 20 := by
  rw [show 33 = 3 * 11 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_11]
  try norm_num

theorem phi_34 : Nat.totient 34 = 16 := by
  rw [show 34 = 2 * 17 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_17]
  try norm_num

theorem phi_35 : Nat.totient 35 = 24 := by
  rw [show 35 = 5 * 7 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_7]
  try norm_num

theorem phi_36 : Nat.totient 36 = 12 := by
  rw [show 36 = 2 * 18 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_18]
  try norm_num

theorem phi_37 : Nat.totient 37 = 36 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_38 : Nat.totient 38 = 18 := by
  rw [show 38 = 2 * 19 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_19]
  try norm_num

theorem phi_39 : Nat.totient 39 = 24 := by
  rw [show 39 = 3 * 13 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_13]
  try norm_num

theorem phi_40 : Nat.totient 40 = 16 := by
  rw [show 40 = 2 * 20 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_20]
  try norm_num

theorem phi_41 : Nat.totient 41 = 40 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_42 : Nat.totient 42 = 12 := by
  rw [show 42 = 2 * 21 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_21]
  try norm_num

theorem phi_43 : Nat.totient 43 = 42 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_44 : Nat.totient 44 = 20 := by
  rw [show 44 = 2 * 22 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_22]
  try norm_num

theorem phi_45 : Nat.totient 45 = 24 := by
  rw [show 45 = 3 * 15 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_15]
  try norm_num

theorem phi_46 : Nat.totient 46 = 22 := by
  rw [show 46 = 2 * 23 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_23]
  try norm_num

theorem phi_47 : Nat.totient 47 = 46 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_48 : Nat.totient 48 = 16 := by
  rw [show 48 = 2 * 24 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_24]
  try norm_num

theorem phi_49 : Nat.totient 49 = 42 := by
  rw [show 49 = 7 * 7 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_7]
  try norm_num

theorem phi_50 : Nat.totient 50 = 20 := by
  rw [show 50 = 2 * 25 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_25]
  try norm_num

theorem phi_51 : Nat.totient 51 = 32 := by
  rw [show 51 = 3 * 17 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_17]
  try norm_num

theorem phi_52 : Nat.totient 52 = 24 := by
  rw [show 52 = 2 * 26 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_26]
  try norm_num

theorem phi_53 : Nat.totient 53 = 52 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_54 : Nat.totient 54 = 18 := by
  rw [show 54 = 2 * 27 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_27]
  try norm_num

theorem phi_55 : Nat.totient 55 = 40 := by
  rw [show 55 = 5 * 11 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_11]
  try norm_num

theorem phi_56 : Nat.totient 56 = 24 := by
  rw [show 56 = 2 * 28 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_28]
  try norm_num

theorem phi_57 : Nat.totient 57 = 36 := by
  rw [show 57 = 3 * 19 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_19]
  try norm_num

theorem phi_58 : Nat.totient 58 = 28 := by
  rw [show 58 = 2 * 29 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_29]
  try norm_num

theorem phi_59 : Nat.totient 59 = 58 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_60 : Nat.totient 60 = 16 := by
  rw [show 60 = 2 * 30 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_30]
  try norm_num

theorem phi_61 : Nat.totient 61 = 60 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_62 : Nat.totient 62 = 30 := by
  rw [show 62 = 2 * 31 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_31]
  try norm_num

theorem phi_63 : Nat.totient 63 = 36 := by
  rw [show 63 = 3 * 21 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_21]
  try norm_num

theorem phi_64 : Nat.totient 64 = 32 := by
  rw [show 64 = 2 * 32 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_32]
  try norm_num

theorem phi_65 : Nat.totient 65 = 48 := by
  rw [show 65 = 5 * 13 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_13]
  try norm_num

theorem phi_66 : Nat.totient 66 = 20 := by
  rw [show 66 = 2 * 33 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_33]
  try norm_num

theorem phi_67 : Nat.totient 67 = 66 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_68 : Nat.totient 68 = 32 := by
  rw [show 68 = 2 * 34 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_34]
  try norm_num

theorem phi_69 : Nat.totient 69 = 44 := by
  rw [show 69 = 3 * 23 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_23]
  try norm_num

theorem phi_70 : Nat.totient 70 = 24 := by
  rw [show 70 = 2 * 35 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_35]
  try norm_num

theorem phi_71 : Nat.totient 71 = 70 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_72 : Nat.totient 72 = 24 := by
  rw [show 72 = 2 * 36 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_36]
  try norm_num

theorem phi_73 : Nat.totient 73 = 72 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_74 : Nat.totient 74 = 36 := by
  rw [show 74 = 2 * 37 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_37]
  try norm_num

theorem phi_75 : Nat.totient 75 = 40 := by
  rw [show 75 = 3 * 25 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_25]
  try norm_num

theorem phi_76 : Nat.totient 76 = 36 := by
  rw [show 76 = 2 * 38 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_38]
  try norm_num

theorem phi_77 : Nat.totient 77 = 60 := by
  rw [show 77 = 7 * 11 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_11]
  try norm_num

theorem phi_78 : Nat.totient 78 = 24 := by
  rw [show 78 = 2 * 39 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_39]
  try norm_num

theorem phi_79 : Nat.totient 79 = 78 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_80 : Nat.totient 80 = 32 := by
  rw [show 80 = 2 * 40 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_40]
  try norm_num

theorem phi_81 : Nat.totient 81 = 54 := by
  rw [show 81 = 3 * 27 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_27]
  try norm_num

theorem phi_82 : Nat.totient 82 = 40 := by
  rw [show 82 = 2 * 41 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_41]
  try norm_num

theorem phi_83 : Nat.totient 83 = 82 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_84 : Nat.totient 84 = 24 := by
  rw [show 84 = 2 * 42 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_42]
  try norm_num

theorem phi_85 : Nat.totient 85 = 64 := by
  rw [show 85 = 5 * 17 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_17]
  try norm_num

theorem phi_86 : Nat.totient 86 = 42 := by
  rw [show 86 = 2 * 43 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_43]
  try norm_num

theorem phi_87 : Nat.totient 87 = 56 := by
  rw [show 87 = 3 * 29 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_29]
  try norm_num

theorem phi_88 : Nat.totient 88 = 40 := by
  rw [show 88 = 2 * 44 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_44]
  try norm_num

theorem phi_89 : Nat.totient 89 = 88 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_90 : Nat.totient 90 = 24 := by
  rw [show 90 = 2 * 45 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_45]
  try norm_num

theorem phi_91 : Nat.totient 91 = 72 := by
  rw [show 91 = 7 * 13 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_13]
  try norm_num

theorem phi_92 : Nat.totient 92 = 44 := by
  rw [show 92 = 2 * 46 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_46]
  try norm_num

theorem phi_93 : Nat.totient 93 = 60 := by
  rw [show 93 = 3 * 31 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_31]
  try norm_num

theorem phi_94 : Nat.totient 94 = 46 := by
  rw [show 94 = 2 * 47 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_47]
  try norm_num

theorem phi_95 : Nat.totient 95 = 72 := by
  rw [show 95 = 5 * 19 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_19]
  try norm_num

theorem phi_96 : Nat.totient 96 = 32 := by
  rw [show 96 = 2 * 48 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_48]
  try norm_num

theorem phi_97 : Nat.totient 97 = 96 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_98 : Nat.totient 98 = 42 := by
  rw [show 98 = 2 * 49 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_49]
  try norm_num

theorem phi_99 : Nat.totient 99 = 60 := by
  rw [show 99 = 3 * 33 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_33]
  try norm_num

theorem phi_100 : Nat.totient 100 = 40 := by
  rw [show 100 = 2 * 50 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_50]
  try norm_num

theorem phi_101 : Nat.totient 101 = 100 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_102 : Nat.totient 102 = 32 := by
  rw [show 102 = 2 * 51 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_51]
  try norm_num

theorem phi_103 : Nat.totient 103 = 102 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_104 : Nat.totient 104 = 48 := by
  rw [show 104 = 2 * 52 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_52]
  try norm_num

theorem phi_105 : Nat.totient 105 = 48 := by
  rw [show 105 = 3 * 35 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_35]
  try norm_num

theorem phi_106 : Nat.totient 106 = 52 := by
  rw [show 106 = 2 * 53 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_53]
  try norm_num

theorem phi_107 : Nat.totient 107 = 106 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_108 : Nat.totient 108 = 36 := by
  rw [show 108 = 2 * 54 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_54]
  try norm_num

theorem phi_109 : Nat.totient 109 = 108 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_110 : Nat.totient 110 = 40 := by
  rw [show 110 = 2 * 55 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_55]
  try norm_num

theorem phi_111 : Nat.totient 111 = 72 := by
  rw [show 111 = 3 * 37 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_37]
  try norm_num

theorem phi_112 : Nat.totient 112 = 48 := by
  rw [show 112 = 2 * 56 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_56]
  try norm_num

theorem phi_113 : Nat.totient 113 = 112 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_114 : Nat.totient 114 = 36 := by
  rw [show 114 = 2 * 57 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_57]
  try norm_num

theorem phi_115 : Nat.totient 115 = 88 := by
  rw [show 115 = 5 * 23 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_23]
  try norm_num

theorem phi_116 : Nat.totient 116 = 56 := by
  rw [show 116 = 2 * 58 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_58]
  try norm_num

theorem phi_117 : Nat.totient 117 = 72 := by
  rw [show 117 = 3 * 39 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_39]
  try norm_num

theorem phi_118 : Nat.totient 118 = 58 := by
  rw [show 118 = 2 * 59 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_59]
  try norm_num

theorem phi_119 : Nat.totient 119 = 96 := by
  rw [show 119 = 7 * 17 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_17]
  try norm_num

theorem phi_120 : Nat.totient 120 = 32 := by
  rw [show 120 = 2 * 60 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_60]
  try norm_num

theorem phi_121 : Nat.totient 121 = 110 := by
  rw [show 121 = 11 * 11 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_11]
  try norm_num

theorem phi_122 : Nat.totient 122 = 60 := by
  rw [show 122 = 2 * 61 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_61]
  try norm_num

theorem phi_123 : Nat.totient 123 = 80 := by
  rw [show 123 = 3 * 41 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_41]
  try norm_num

theorem phi_124 : Nat.totient 124 = 60 := by
  rw [show 124 = 2 * 62 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_62]
  try norm_num

theorem phi_125 : Nat.totient 125 = 100 := by
  rw [show 125 = 5 * 25 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_25]
  try norm_num

theorem phi_126 : Nat.totient 126 = 36 := by
  rw [show 126 = 2 * 63 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_63]
  try norm_num

theorem phi_127 : Nat.totient 127 = 126 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_128 : Nat.totient 128 = 64 := by
  rw [show 128 = 2 * 64 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_64]
  try norm_num

theorem phi_129 : Nat.totient 129 = 84 := by
  rw [show 129 = 3 * 43 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_43]
  try norm_num

theorem phi_130 : Nat.totient 130 = 48 := by
  rw [show 130 = 2 * 65 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_65]
  try norm_num

theorem phi_131 : Nat.totient 131 = 130 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_132 : Nat.totient 132 = 40 := by
  rw [show 132 = 2 * 66 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_66]
  try norm_num

theorem phi_133 : Nat.totient 133 = 108 := by
  rw [show 133 = 7 * 19 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_19]
  try norm_num

theorem phi_134 : Nat.totient 134 = 66 := by
  rw [show 134 = 2 * 67 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_67]
  try norm_num

theorem phi_135 : Nat.totient 135 = 72 := by
  rw [show 135 = 3 * 45 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_45]
  try norm_num

theorem phi_136 : Nat.totient 136 = 64 := by
  rw [show 136 = 2 * 68 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_68]
  try norm_num

theorem phi_137 : Nat.totient 137 = 136 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_138 : Nat.totient 138 = 44 := by
  rw [show 138 = 2 * 69 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_69]
  try norm_num

theorem phi_139 : Nat.totient 139 = 138 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_140 : Nat.totient 140 = 48 := by
  rw [show 140 = 2 * 70 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_70]
  try norm_num

theorem phi_141 : Nat.totient 141 = 92 := by
  rw [show 141 = 3 * 47 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_47]
  try norm_num

theorem phi_142 : Nat.totient 142 = 70 := by
  rw [show 142 = 2 * 71 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_71]
  try norm_num

theorem phi_143 : Nat.totient 143 = 120 := by
  rw [show 143 = 11 * 13 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_13]
  try norm_num

theorem phi_144 : Nat.totient 144 = 48 := by
  rw [show 144 = 2 * 72 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_72]
  try norm_num

theorem phi_145 : Nat.totient 145 = 112 := by
  rw [show 145 = 5 * 29 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_29]
  try norm_num

theorem phi_146 : Nat.totient 146 = 72 := by
  rw [show 146 = 2 * 73 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_73]
  try norm_num

theorem phi_147 : Nat.totient 147 = 84 := by
  rw [show 147 = 3 * 49 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_49]
  try norm_num

theorem phi_148 : Nat.totient 148 = 72 := by
  rw [show 148 = 2 * 74 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_74]
  try norm_num

theorem phi_149 : Nat.totient 149 = 148 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_150 : Nat.totient 150 = 40 := by
  rw [show 150 = 2 * 75 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_75]
  try norm_num

theorem phi_151 : Nat.totient 151 = 150 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_152 : Nat.totient 152 = 72 := by
  rw [show 152 = 2 * 76 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_76]
  try norm_num

theorem phi_153 : Nat.totient 153 = 96 := by
  rw [show 153 = 3 * 51 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_51]
  try norm_num

theorem phi_154 : Nat.totient 154 = 60 := by
  rw [show 154 = 2 * 77 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_77]
  try norm_num

theorem phi_155 : Nat.totient 155 = 120 := by
  rw [show 155 = 5 * 31 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_31]
  try norm_num

theorem phi_156 : Nat.totient 156 = 48 := by
  rw [show 156 = 2 * 78 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_78]
  try norm_num

theorem phi_157 : Nat.totient 157 = 156 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_158 : Nat.totient 158 = 78 := by
  rw [show 158 = 2 * 79 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_79]
  try norm_num

theorem phi_159 : Nat.totient 159 = 104 := by
  rw [show 159 = 3 * 53 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_53]
  try norm_num

theorem phi_160 : Nat.totient 160 = 64 := by
  rw [show 160 = 2 * 80 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_80]
  try norm_num

theorem phi_161 : Nat.totient 161 = 132 := by
  rw [show 161 = 7 * 23 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_23]
  try norm_num

theorem phi_162 : Nat.totient 162 = 54 := by
  rw [show 162 = 2 * 81 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_81]
  try norm_num

theorem phi_163 : Nat.totient 163 = 162 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_164 : Nat.totient 164 = 80 := by
  rw [show 164 = 2 * 82 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_82]
  try norm_num

theorem phi_165 : Nat.totient 165 = 80 := by
  rw [show 165 = 3 * 55 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_55]
  try norm_num

theorem phi_166 : Nat.totient 166 = 82 := by
  rw [show 166 = 2 * 83 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_83]
  try norm_num

theorem phi_167 : Nat.totient 167 = 166 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_168 : Nat.totient 168 = 48 := by
  rw [show 168 = 2 * 84 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_84]
  try norm_num

theorem phi_169 : Nat.totient 169 = 156 := by
  rw [show 169 = 13 * 13 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_13]
  try norm_num

theorem phi_170 : Nat.totient 170 = 64 := by
  rw [show 170 = 2 * 85 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_85]
  try norm_num

theorem phi_171 : Nat.totient 171 = 108 := by
  rw [show 171 = 3 * 57 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_57]
  try norm_num

theorem phi_172 : Nat.totient 172 = 84 := by
  rw [show 172 = 2 * 86 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_86]
  try norm_num

theorem phi_173 : Nat.totient 173 = 172 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_174 : Nat.totient 174 = 56 := by
  rw [show 174 = 2 * 87 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_87]
  try norm_num

theorem phi_175 : Nat.totient 175 = 120 := by
  rw [show 175 = 5 * 35 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_35]
  try norm_num

theorem phi_176 : Nat.totient 176 = 80 := by
  rw [show 176 = 2 * 88 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_88]
  try norm_num

theorem phi_177 : Nat.totient 177 = 116 := by
  rw [show 177 = 3 * 59 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_59]
  try norm_num

theorem phi_178 : Nat.totient 178 = 88 := by
  rw [show 178 = 2 * 89 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_89]
  try norm_num

theorem phi_179 : Nat.totient 179 = 178 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_180 : Nat.totient 180 = 48 := by
  rw [show 180 = 2 * 90 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_90]
  try norm_num

theorem phi_181 : Nat.totient 181 = 180 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_182 : Nat.totient 182 = 72 := by
  rw [show 182 = 2 * 91 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_91]
  try norm_num

theorem phi_183 : Nat.totient 183 = 120 := by
  rw [show 183 = 3 * 61 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_61]
  try norm_num

theorem phi_184 : Nat.totient 184 = 88 := by
  rw [show 184 = 2 * 92 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_92]
  try norm_num

theorem phi_185 : Nat.totient 185 = 144 := by
  rw [show 185 = 5 * 37 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_37]
  try norm_num

theorem phi_186 : Nat.totient 186 = 60 := by
  rw [show 186 = 2 * 93 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_93]
  try norm_num

theorem phi_187 : Nat.totient 187 = 160 := by
  rw [show 187 = 11 * 17 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_17]
  try norm_num

theorem phi_188 : Nat.totient 188 = 92 := by
  rw [show 188 = 2 * 94 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_94]
  try norm_num

theorem phi_189 : Nat.totient 189 = 108 := by
  rw [show 189 = 3 * 63 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_63]
  try norm_num

theorem phi_190 : Nat.totient 190 = 72 := by
  rw [show 190 = 2 * 95 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_95]
  try norm_num

theorem phi_191 : Nat.totient 191 = 190 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_192 : Nat.totient 192 = 64 := by
  rw [show 192 = 2 * 96 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_96]
  try norm_num

theorem phi_193 : Nat.totient 193 = 192 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_194 : Nat.totient 194 = 96 := by
  rw [show 194 = 2 * 97 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_97]
  try norm_num

theorem phi_195 : Nat.totient 195 = 96 := by
  rw [show 195 = 3 * 65 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_65]
  try norm_num

theorem phi_196 : Nat.totient 196 = 84 := by
  rw [show 196 = 2 * 98 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_98]
  try norm_num

theorem phi_197 : Nat.totient 197 = 196 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_198 : Nat.totient 198 = 60 := by
  rw [show 198 = 2 * 99 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_99]
  try norm_num

theorem phi_199 : Nat.totient 199 = 198 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_200 : Nat.totient 200 = 80 := by
  rw [show 200 = 2 * 100 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_100]
  try norm_num

theorem phi_201 : Nat.totient 201 = 132 := by
  rw [show 201 = 3 * 67 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_67]
  try norm_num

theorem phi_202 : Nat.totient 202 = 100 := by
  rw [show 202 = 2 * 101 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_101]
  try norm_num

theorem phi_203 : Nat.totient 203 = 168 := by
  rw [show 203 = 7 * 29 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_29]
  try norm_num

theorem phi_204 : Nat.totient 204 = 64 := by
  rw [show 204 = 2 * 102 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_102]
  try norm_num

theorem phi_205 : Nat.totient 205 = 160 := by
  rw [show 205 = 5 * 41 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_41]
  try norm_num

theorem phi_206 : Nat.totient 206 = 102 := by
  rw [show 206 = 2 * 103 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_103]
  try norm_num

theorem phi_207 : Nat.totient 207 = 132 := by
  rw [show 207 = 3 * 69 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_69]
  try norm_num

theorem phi_208 : Nat.totient 208 = 96 := by
  rw [show 208 = 2 * 104 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_104]
  try norm_num

theorem phi_209 : Nat.totient 209 = 180 := by
  rw [show 209 = 11 * 19 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_19]
  try norm_num

theorem phi_210 : Nat.totient 210 = 48 := by
  rw [show 210 = 2 * 105 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_105]
  try norm_num

theorem phi_211 : Nat.totient 211 = 210 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_212 : Nat.totient 212 = 104 := by
  rw [show 212 = 2 * 106 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_106]
  try norm_num

theorem phi_213 : Nat.totient 213 = 140 := by
  rw [show 213 = 3 * 71 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_71]
  try norm_num

theorem phi_214 : Nat.totient 214 = 106 := by
  rw [show 214 = 2 * 107 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_107]
  try norm_num

theorem phi_215 : Nat.totient 215 = 168 := by
  rw [show 215 = 5 * 43 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_43]
  try norm_num

theorem phi_216 : Nat.totient 216 = 72 := by
  rw [show 216 = 2 * 108 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_108]
  try norm_num

theorem phi_217 : Nat.totient 217 = 180 := by
  rw [show 217 = 7 * 31 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_31]
  try norm_num

theorem phi_218 : Nat.totient 218 = 108 := by
  rw [show 218 = 2 * 109 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_109]
  try norm_num

theorem phi_219 : Nat.totient 219 = 144 := by
  rw [show 219 = 3 * 73 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_73]
  try norm_num

theorem phi_220 : Nat.totient 220 = 80 := by
  rw [show 220 = 2 * 110 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_110]
  try norm_num

theorem phi_221 : Nat.totient 221 = 192 := by
  rw [show 221 = 13 * 17 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_17]
  try norm_num

theorem phi_222 : Nat.totient 222 = 72 := by
  rw [show 222 = 2 * 111 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_111]
  try norm_num

theorem phi_223 : Nat.totient 223 = 222 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_224 : Nat.totient 224 = 96 := by
  rw [show 224 = 2 * 112 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_112]
  try norm_num

theorem phi_225 : Nat.totient 225 = 120 := by
  rw [show 225 = 3 * 75 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_75]
  try norm_num

theorem phi_226 : Nat.totient 226 = 112 := by
  rw [show 226 = 2 * 113 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_113]
  try norm_num

theorem phi_227 : Nat.totient 227 = 226 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_228 : Nat.totient 228 = 72 := by
  rw [show 228 = 2 * 114 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_114]
  try norm_num

theorem phi_229 : Nat.totient 229 = 228 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_230 : Nat.totient 230 = 88 := by
  rw [show 230 = 2 * 115 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_115]
  try norm_num

theorem phi_231 : Nat.totient 231 = 120 := by
  rw [show 231 = 3 * 77 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_77]
  try norm_num

theorem phi_232 : Nat.totient 232 = 112 := by
  rw [show 232 = 2 * 116 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_116]
  try norm_num

theorem phi_233 : Nat.totient 233 = 232 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_234 : Nat.totient 234 = 72 := by
  rw [show 234 = 2 * 117 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_117]
  try norm_num

theorem phi_235 : Nat.totient 235 = 184 := by
  rw [show 235 = 5 * 47 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_47]
  try norm_num

theorem phi_236 : Nat.totient 236 = 116 := by
  rw [show 236 = 2 * 118 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_118]
  try norm_num

theorem phi_237 : Nat.totient 237 = 156 := by
  rw [show 237 = 3 * 79 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_79]
  try norm_num

theorem phi_238 : Nat.totient 238 = 96 := by
  rw [show 238 = 2 * 119 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_119]
  try norm_num

theorem phi_239 : Nat.totient 239 = 238 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_240 : Nat.totient 240 = 64 := by
  rw [show 240 = 2 * 120 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_120]
  try norm_num

theorem phi_241 : Nat.totient 241 = 240 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_242 : Nat.totient 242 = 110 := by
  rw [show 242 = 2 * 121 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_121]
  try norm_num

theorem phi_243 : Nat.totient 243 = 162 := by
  rw [show 243 = 3 * 81 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_81]
  try norm_num

theorem phi_244 : Nat.totient 244 = 120 := by
  rw [show 244 = 2 * 122 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_122]
  try norm_num

theorem phi_245 : Nat.totient 245 = 168 := by
  rw [show 245 = 5 * 49 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_49]
  try norm_num

theorem phi_246 : Nat.totient 246 = 80 := by
  rw [show 246 = 2 * 123 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_123]
  try norm_num

theorem phi_247 : Nat.totient 247 = 216 := by
  rw [show 247 = 13 * 19 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_19]
  try norm_num

theorem phi_248 : Nat.totient 248 = 120 := by
  rw [show 248 = 2 * 124 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_124]
  try norm_num

theorem phi_249 : Nat.totient 249 = 164 := by
  rw [show 249 = 3 * 83 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_83]
  try norm_num

theorem phi_250 : Nat.totient 250 = 100 := by
  rw [show 250 = 2 * 125 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_125]
  try norm_num

theorem phi_251 : Nat.totient 251 = 250 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_252 : Nat.totient 252 = 72 := by
  rw [show 252 = 2 * 126 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_126]
  try norm_num

theorem phi_253 : Nat.totient 253 = 220 := by
  rw [show 253 = 11 * 23 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_23]
  try norm_num

theorem phi_254 : Nat.totient 254 = 126 := by
  rw [show 254 = 2 * 127 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_127]
  try norm_num

theorem phi_255 : Nat.totient 255 = 128 := by
  rw [show 255 = 3 * 85 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_85]
  try norm_num

theorem phi_256 : Nat.totient 256 = 128 := by
  rw [show 256 = 2 * 128 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_128]
  try norm_num

theorem phi_257 : Nat.totient 257 = 256 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_258 : Nat.totient 258 = 84 := by
  rw [show 258 = 2 * 129 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_129]
  try norm_num

theorem phi_259 : Nat.totient 259 = 216 := by
  rw [show 259 = 7 * 37 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_37]
  try norm_num

theorem phi_260 : Nat.totient 260 = 96 := by
  rw [show 260 = 2 * 130 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_130]
  try norm_num

theorem phi_261 : Nat.totient 261 = 168 := by
  rw [show 261 = 3 * 87 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_87]
  try norm_num

theorem phi_262 : Nat.totient 262 = 130 := by
  rw [show 262 = 2 * 131 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_131]
  try norm_num

theorem phi_263 : Nat.totient 263 = 262 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_264 : Nat.totient 264 = 80 := by
  rw [show 264 = 2 * 132 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_132]
  try norm_num

theorem phi_265 : Nat.totient 265 = 208 := by
  rw [show 265 = 5 * 53 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_53]
  try norm_num

theorem phi_266 : Nat.totient 266 = 108 := by
  rw [show 266 = 2 * 133 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_133]
  try norm_num

theorem phi_267 : Nat.totient 267 = 176 := by
  rw [show 267 = 3 * 89 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_89]
  try norm_num

theorem phi_268 : Nat.totient 268 = 132 := by
  rw [show 268 = 2 * 134 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_134]
  try norm_num

theorem phi_269 : Nat.totient 269 = 268 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_270 : Nat.totient 270 = 72 := by
  rw [show 270 = 2 * 135 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_135]
  try norm_num

theorem phi_271 : Nat.totient 271 = 270 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_272 : Nat.totient 272 = 128 := by
  rw [show 272 = 2 * 136 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_136]
  try norm_num

theorem phi_273 : Nat.totient 273 = 144 := by
  rw [show 273 = 3 * 91 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_91]
  try norm_num

theorem phi_274 : Nat.totient 274 = 136 := by
  rw [show 274 = 2 * 137 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_137]
  try norm_num

theorem phi_275 : Nat.totient 275 = 200 := by
  rw [show 275 = 5 * 55 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_55]
  try norm_num

theorem phi_276 : Nat.totient 276 = 88 := by
  rw [show 276 = 2 * 138 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_138]
  try norm_num

theorem phi_277 : Nat.totient 277 = 276 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_278 : Nat.totient 278 = 138 := by
  rw [show 278 = 2 * 139 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_139]
  try norm_num

theorem phi_279 : Nat.totient 279 = 180 := by
  rw [show 279 = 3 * 93 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_93]
  try norm_num

theorem phi_280 : Nat.totient 280 = 96 := by
  rw [show 280 = 2 * 140 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_140]
  try norm_num

theorem phi_281 : Nat.totient 281 = 280 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_282 : Nat.totient 282 = 92 := by
  rw [show 282 = 2 * 141 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_141]
  try norm_num

theorem phi_283 : Nat.totient 283 = 282 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_284 : Nat.totient 284 = 140 := by
  rw [show 284 = 2 * 142 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_142]
  try norm_num

theorem phi_285 : Nat.totient 285 = 144 := by
  rw [show 285 = 3 * 95 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_95]
  try norm_num

theorem phi_286 : Nat.totient 286 = 120 := by
  rw [show 286 = 2 * 143 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_143]
  try norm_num

theorem phi_287 : Nat.totient 287 = 240 := by
  rw [show 287 = 7 * 41 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_41]
  try norm_num

theorem phi_288 : Nat.totient 288 = 96 := by
  rw [show 288 = 2 * 144 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_144]
  try norm_num

theorem phi_289 : Nat.totient 289 = 272 := by
  rw [show 289 = 17 * 17 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_17]
  try norm_num

theorem phi_290 : Nat.totient 290 = 112 := by
  rw [show 290 = 2 * 145 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_145]
  try norm_num

theorem phi_291 : Nat.totient 291 = 192 := by
  rw [show 291 = 3 * 97 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_97]
  try norm_num

theorem phi_292 : Nat.totient 292 = 144 := by
  rw [show 292 = 2 * 146 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_146]
  try norm_num

theorem phi_293 : Nat.totient 293 = 292 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_294 : Nat.totient 294 = 84 := by
  rw [show 294 = 2 * 147 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_147]
  try norm_num

theorem phi_295 : Nat.totient 295 = 232 := by
  rw [show 295 = 5 * 59 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_59]
  try norm_num

theorem phi_296 : Nat.totient 296 = 144 := by
  rw [show 296 = 2 * 148 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_148]
  try norm_num

theorem phi_297 : Nat.totient 297 = 180 := by
  rw [show 297 = 3 * 99 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_99]
  try norm_num

theorem phi_298 : Nat.totient 298 = 148 := by
  rw [show 298 = 2 * 149 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_149]
  try norm_num

theorem phi_299 : Nat.totient 299 = 264 := by
  rw [show 299 = 13 * 23 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_23]
  try norm_num

theorem phi_300 : Nat.totient 300 = 80 := by
  rw [show 300 = 2 * 150 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_150]
  try norm_num

theorem phi_301 : Nat.totient 301 = 252 := by
  rw [show 301 = 7 * 43 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_43]
  try norm_num

theorem phi_302 : Nat.totient 302 = 150 := by
  rw [show 302 = 2 * 151 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_151]
  try norm_num

theorem phi_303 : Nat.totient 303 = 200 := by
  rw [show 303 = 3 * 101 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_101]
  try norm_num

theorem phi_304 : Nat.totient 304 = 144 := by
  rw [show 304 = 2 * 152 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_152]
  try norm_num

theorem phi_305 : Nat.totient 305 = 240 := by
  rw [show 305 = 5 * 61 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_61]
  try norm_num

theorem phi_306 : Nat.totient 306 = 96 := by
  rw [show 306 = 2 * 153 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_153]
  try norm_num

theorem phi_307 : Nat.totient 307 = 306 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_308 : Nat.totient 308 = 120 := by
  rw [show 308 = 2 * 154 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_154]
  try norm_num

theorem phi_309 : Nat.totient 309 = 204 := by
  rw [show 309 = 3 * 103 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_103]
  try norm_num

theorem phi_310 : Nat.totient 310 = 120 := by
  rw [show 310 = 2 * 155 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_155]
  try norm_num

theorem phi_311 : Nat.totient 311 = 310 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_312 : Nat.totient 312 = 96 := by
  rw [show 312 = 2 * 156 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_156]
  try norm_num

theorem phi_313 : Nat.totient 313 = 312 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_314 : Nat.totient 314 = 156 := by
  rw [show 314 = 2 * 157 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_157]
  try norm_num

theorem phi_315 : Nat.totient 315 = 144 := by
  rw [show 315 = 3 * 105 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_105]
  try norm_num

theorem phi_316 : Nat.totient 316 = 156 := by
  rw [show 316 = 2 * 158 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_158]
  try norm_num

theorem phi_317 : Nat.totient 317 = 316 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_318 : Nat.totient 318 = 104 := by
  rw [show 318 = 2 * 159 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_159]
  try norm_num

theorem phi_319 : Nat.totient 319 = 280 := by
  rw [show 319 = 11 * 29 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_29]
  try norm_num

theorem phi_320 : Nat.totient 320 = 128 := by
  rw [show 320 = 2 * 160 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_160]
  try norm_num

theorem phi_321 : Nat.totient 321 = 212 := by
  rw [show 321 = 3 * 107 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_107]
  try norm_num

theorem phi_322 : Nat.totient 322 = 132 := by
  rw [show 322 = 2 * 161 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_161]
  try norm_num

theorem phi_323 : Nat.totient 323 = 288 := by
  rw [show 323 = 17 * 19 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_19]
  try norm_num

theorem phi_324 : Nat.totient 324 = 108 := by
  rw [show 324 = 2 * 162 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_162]
  try norm_num

theorem phi_325 : Nat.totient 325 = 240 := by
  rw [show 325 = 5 * 65 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_65]
  try norm_num

theorem phi_326 : Nat.totient 326 = 162 := by
  rw [show 326 = 2 * 163 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_163]
  try norm_num

theorem phi_327 : Nat.totient 327 = 216 := by
  rw [show 327 = 3 * 109 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_109]
  try norm_num

theorem phi_328 : Nat.totient 328 = 160 := by
  rw [show 328 = 2 * 164 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_164]
  try norm_num

theorem phi_329 : Nat.totient 329 = 276 := by
  rw [show 329 = 7 * 47 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_47]
  try norm_num

theorem phi_330 : Nat.totient 330 = 80 := by
  rw [show 330 = 2 * 165 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_165]
  try norm_num

theorem phi_331 : Nat.totient 331 = 330 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_332 : Nat.totient 332 = 164 := by
  rw [show 332 = 2 * 166 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_166]
  try norm_num

theorem phi_333 : Nat.totient 333 = 216 := by
  rw [show 333 = 3 * 111 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_111]
  try norm_num

theorem phi_334 : Nat.totient 334 = 166 := by
  rw [show 334 = 2 * 167 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_167]
  try norm_num

theorem phi_335 : Nat.totient 335 = 264 := by
  rw [show 335 = 5 * 67 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_67]
  try norm_num

theorem phi_336 : Nat.totient 336 = 96 := by
  rw [show 336 = 2 * 168 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_168]
  try norm_num

theorem phi_337 : Nat.totient 337 = 336 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_338 : Nat.totient 338 = 156 := by
  rw [show 338 = 2 * 169 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_169]
  try norm_num

theorem phi_339 : Nat.totient 339 = 224 := by
  rw [show 339 = 3 * 113 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_113]
  try norm_num

theorem phi_340 : Nat.totient 340 = 128 := by
  rw [show 340 = 2 * 170 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_170]
  try norm_num

theorem phi_341 : Nat.totient 341 = 300 := by
  rw [show 341 = 11 * 31 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_31]
  try norm_num

theorem phi_342 : Nat.totient 342 = 108 := by
  rw [show 342 = 2 * 171 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_171]
  try norm_num

theorem phi_343 : Nat.totient 343 = 294 := by
  rw [show 343 = 7 * 49 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_49]
  try norm_num

theorem phi_344 : Nat.totient 344 = 168 := by
  rw [show 344 = 2 * 172 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_172]
  try norm_num

theorem phi_345 : Nat.totient 345 = 176 := by
  rw [show 345 = 3 * 115 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_115]
  try norm_num

theorem phi_346 : Nat.totient 346 = 172 := by
  rw [show 346 = 2 * 173 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_173]
  try norm_num

theorem phi_347 : Nat.totient 347 = 346 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_348 : Nat.totient 348 = 112 := by
  rw [show 348 = 2 * 174 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_174]
  try norm_num

theorem phi_349 : Nat.totient 349 = 348 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_350 : Nat.totient 350 = 120 := by
  rw [show 350 = 2 * 175 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_175]
  try norm_num

theorem phi_351 : Nat.totient 351 = 216 := by
  rw [show 351 = 3 * 117 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_117]
  try norm_num

theorem phi_352 : Nat.totient 352 = 160 := by
  rw [show 352 = 2 * 176 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_176]
  try norm_num

theorem phi_353 : Nat.totient 353 = 352 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_354 : Nat.totient 354 = 116 := by
  rw [show 354 = 2 * 177 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_177]
  try norm_num

theorem phi_355 : Nat.totient 355 = 280 := by
  rw [show 355 = 5 * 71 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_71]
  try norm_num

theorem phi_356 : Nat.totient 356 = 176 := by
  rw [show 356 = 2 * 178 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_178]
  try norm_num

theorem phi_357 : Nat.totient 357 = 192 := by
  rw [show 357 = 3 * 119 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_119]
  try norm_num

theorem phi_358 : Nat.totient 358 = 178 := by
  rw [show 358 = 2 * 179 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_179]
  try norm_num

theorem phi_359 : Nat.totient 359 = 358 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_360 : Nat.totient 360 = 96 := by
  rw [show 360 = 2 * 180 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_180]
  try norm_num

theorem phi_361 : Nat.totient 361 = 342 := by
  rw [show 361 = 19 * 19 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_19]
  try norm_num

theorem phi_362 : Nat.totient 362 = 180 := by
  rw [show 362 = 2 * 181 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_181]
  try norm_num

theorem phi_363 : Nat.totient 363 = 220 := by
  rw [show 363 = 3 * 121 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_121]
  try norm_num

theorem phi_364 : Nat.totient 364 = 144 := by
  rw [show 364 = 2 * 182 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_182]
  try norm_num

theorem phi_365 : Nat.totient 365 = 288 := by
  rw [show 365 = 5 * 73 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_73]
  try norm_num

theorem phi_366 : Nat.totient 366 = 120 := by
  rw [show 366 = 2 * 183 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_183]
  try norm_num

theorem phi_367 : Nat.totient 367 = 366 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_368 : Nat.totient 368 = 176 := by
  rw [show 368 = 2 * 184 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_184]
  try norm_num

theorem phi_369 : Nat.totient 369 = 240 := by
  rw [show 369 = 3 * 123 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_123]
  try norm_num

theorem phi_370 : Nat.totient 370 = 144 := by
  rw [show 370 = 2 * 185 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_185]
  try norm_num

theorem phi_371 : Nat.totient 371 = 312 := by
  rw [show 371 = 7 * 53 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_53]
  try norm_num

theorem phi_372 : Nat.totient 372 = 120 := by
  rw [show 372 = 2 * 186 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_186]
  try norm_num

theorem phi_373 : Nat.totient 373 = 372 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_374 : Nat.totient 374 = 160 := by
  rw [show 374 = 2 * 187 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_187]
  try norm_num

theorem phi_375 : Nat.totient 375 = 200 := by
  rw [show 375 = 3 * 125 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_125]
  try norm_num

theorem phi_376 : Nat.totient 376 = 184 := by
  rw [show 376 = 2 * 188 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_188]
  try norm_num

theorem phi_377 : Nat.totient 377 = 336 := by
  rw [show 377 = 13 * 29 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_29]
  try norm_num

theorem phi_378 : Nat.totient 378 = 108 := by
  rw [show 378 = 2 * 189 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_189]
  try norm_num

theorem phi_379 : Nat.totient 379 = 378 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_380 : Nat.totient 380 = 144 := by
  rw [show 380 = 2 * 190 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_190]
  try norm_num

theorem phi_381 : Nat.totient 381 = 252 := by
  rw [show 381 = 3 * 127 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_127]
  try norm_num

theorem phi_382 : Nat.totient 382 = 190 := by
  rw [show 382 = 2 * 191 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_191]
  try norm_num

theorem phi_383 : Nat.totient 383 = 382 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_384 : Nat.totient 384 = 128 := by
  rw [show 384 = 2 * 192 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_192]
  try norm_num

theorem phi_385 : Nat.totient 385 = 240 := by
  rw [show 385 = 5 * 77 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_77]
  try norm_num

theorem phi_386 : Nat.totient 386 = 192 := by
  rw [show 386 = 2 * 193 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_193]
  try norm_num

theorem phi_387 : Nat.totient 387 = 252 := by
  rw [show 387 = 3 * 129 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_129]
  try norm_num

theorem phi_388 : Nat.totient 388 = 192 := by
  rw [show 388 = 2 * 194 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_194]
  try norm_num

theorem phi_389 : Nat.totient 389 = 388 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_390 : Nat.totient 390 = 96 := by
  rw [show 390 = 2 * 195 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_195]
  try norm_num

theorem phi_391 : Nat.totient 391 = 352 := by
  rw [show 391 = 17 * 23 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_23]
  try norm_num

theorem phi_392 : Nat.totient 392 = 168 := by
  rw [show 392 = 2 * 196 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_196]
  try norm_num

theorem phi_393 : Nat.totient 393 = 260 := by
  rw [show 393 = 3 * 131 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_131]
  try norm_num

theorem phi_394 : Nat.totient 394 = 196 := by
  rw [show 394 = 2 * 197 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_197]
  try norm_num

theorem phi_395 : Nat.totient 395 = 312 := by
  rw [show 395 = 5 * 79 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_79]
  try norm_num

theorem phi_396 : Nat.totient 396 = 120 := by
  rw [show 396 = 2 * 198 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_198]
  try norm_num

theorem phi_397 : Nat.totient 397 = 396 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_398 : Nat.totient 398 = 198 := by
  rw [show 398 = 2 * 199 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_199]
  try norm_num

theorem phi_399 : Nat.totient 399 = 216 := by
  rw [show 399 = 3 * 133 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_133]
  try norm_num

theorem phi_400 : Nat.totient 400 = 160 := by
  rw [show 400 = 2 * 200 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_200]
  try norm_num

theorem phi_401 : Nat.totient 401 = 400 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_402 : Nat.totient 402 = 132 := by
  rw [show 402 = 2 * 201 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_201]
  try norm_num

theorem phi_403 : Nat.totient 403 = 360 := by
  rw [show 403 = 13 * 31 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_31]
  try norm_num

theorem phi_404 : Nat.totient 404 = 200 := by
  rw [show 404 = 2 * 202 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_202]
  try norm_num

theorem phi_405 : Nat.totient 405 = 216 := by
  rw [show 405 = 3 * 135 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_135]
  try norm_num

theorem phi_406 : Nat.totient 406 = 168 := by
  rw [show 406 = 2 * 203 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_203]
  try norm_num

theorem phi_407 : Nat.totient 407 = 360 := by
  rw [show 407 = 11 * 37 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_37]
  try norm_num

theorem phi_408 : Nat.totient 408 = 128 := by
  rw [show 408 = 2 * 204 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_204]
  try norm_num

theorem phi_409 : Nat.totient 409 = 408 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_410 : Nat.totient 410 = 160 := by
  rw [show 410 = 2 * 205 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_205]
  try norm_num

theorem phi_411 : Nat.totient 411 = 272 := by
  rw [show 411 = 3 * 137 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_137]
  try norm_num

theorem phi_412 : Nat.totient 412 = 204 := by
  rw [show 412 = 2 * 206 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_206]
  try norm_num

theorem phi_413 : Nat.totient 413 = 348 := by
  rw [show 413 = 7 * 59 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_59]
  try norm_num

theorem phi_414 : Nat.totient 414 = 132 := by
  rw [show 414 = 2 * 207 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_207]
  try norm_num

theorem phi_415 : Nat.totient 415 = 328 := by
  rw [show 415 = 5 * 83 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_83]
  try norm_num

theorem phi_416 : Nat.totient 416 = 192 := by
  rw [show 416 = 2 * 208 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_208]
  try norm_num

theorem phi_417 : Nat.totient 417 = 276 := by
  rw [show 417 = 3 * 139 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_139]
  try norm_num

theorem phi_418 : Nat.totient 418 = 180 := by
  rw [show 418 = 2 * 209 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_209]
  try norm_num

theorem phi_419 : Nat.totient 419 = 418 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_420 : Nat.totient 420 = 96 := by
  rw [show 420 = 2 * 210 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_210]
  try norm_num

theorem phi_421 : Nat.totient 421 = 420 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_422 : Nat.totient 422 = 210 := by
  rw [show 422 = 2 * 211 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_211]
  try norm_num

theorem phi_423 : Nat.totient 423 = 276 := by
  rw [show 423 = 3 * 141 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_141]
  try norm_num

theorem phi_424 : Nat.totient 424 = 208 := by
  rw [show 424 = 2 * 212 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_212]
  try norm_num

theorem phi_425 : Nat.totient 425 = 320 := by
  rw [show 425 = 5 * 85 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_85]
  try norm_num

theorem phi_426 : Nat.totient 426 = 140 := by
  rw [show 426 = 2 * 213 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_213]
  try norm_num

theorem phi_427 : Nat.totient 427 = 360 := by
  rw [show 427 = 7 * 61 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_61]
  try norm_num

theorem phi_428 : Nat.totient 428 = 212 := by
  rw [show 428 = 2 * 214 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_214]
  try norm_num

theorem phi_429 : Nat.totient 429 = 240 := by
  rw [show 429 = 3 * 143 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_143]
  try norm_num

theorem phi_430 : Nat.totient 430 = 168 := by
  rw [show 430 = 2 * 215 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_215]
  try norm_num

theorem phi_431 : Nat.totient 431 = 430 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_432 : Nat.totient 432 = 144 := by
  rw [show 432 = 2 * 216 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_216]
  try norm_num

theorem phi_433 : Nat.totient 433 = 432 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_434 : Nat.totient 434 = 180 := by
  rw [show 434 = 2 * 217 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_217]
  try norm_num

theorem phi_435 : Nat.totient 435 = 224 := by
  rw [show 435 = 3 * 145 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_145]
  try norm_num

theorem phi_436 : Nat.totient 436 = 216 := by
  rw [show 436 = 2 * 218 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_218]
  try norm_num

theorem phi_437 : Nat.totient 437 = 396 := by
  rw [show 437 = 19 * 23 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_23]
  try norm_num

theorem phi_438 : Nat.totient 438 = 144 := by
  rw [show 438 = 2 * 219 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_219]
  try norm_num

theorem phi_439 : Nat.totient 439 = 438 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_440 : Nat.totient 440 = 160 := by
  rw [show 440 = 2 * 220 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_220]
  try norm_num

theorem phi_441 : Nat.totient 441 = 252 := by
  rw [show 441 = 3 * 147 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_147]
  try norm_num

theorem phi_442 : Nat.totient 442 = 192 := by
  rw [show 442 = 2 * 221 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_221]
  try norm_num

theorem phi_443 : Nat.totient 443 = 442 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_444 : Nat.totient 444 = 144 := by
  rw [show 444 = 2 * 222 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_222]
  try norm_num

theorem phi_445 : Nat.totient 445 = 352 := by
  rw [show 445 = 5 * 89 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_89]
  try norm_num

theorem phi_446 : Nat.totient 446 = 222 := by
  rw [show 446 = 2 * 223 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_223]
  try norm_num

theorem phi_447 : Nat.totient 447 = 296 := by
  rw [show 447 = 3 * 149 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_149]
  try norm_num

theorem phi_448 : Nat.totient 448 = 192 := by
  rw [show 448 = 2 * 224 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_224]
  try norm_num

theorem phi_449 : Nat.totient 449 = 448 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_450 : Nat.totient 450 = 120 := by
  rw [show 450 = 2 * 225 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_225]
  try norm_num

theorem phi_451 : Nat.totient 451 = 400 := by
  rw [show 451 = 11 * 41 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_41]
  try norm_num

theorem phi_452 : Nat.totient 452 = 224 := by
  rw [show 452 = 2 * 226 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_226]
  try norm_num

theorem phi_453 : Nat.totient 453 = 300 := by
  rw [show 453 = 3 * 151 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_151]
  try norm_num

theorem phi_454 : Nat.totient 454 = 226 := by
  rw [show 454 = 2 * 227 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_227]
  try norm_num

theorem phi_455 : Nat.totient 455 = 288 := by
  rw [show 455 = 5 * 91 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_91]
  try norm_num

theorem phi_456 : Nat.totient 456 = 144 := by
  rw [show 456 = 2 * 228 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_228]
  try norm_num

theorem phi_457 : Nat.totient 457 = 456 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_458 : Nat.totient 458 = 228 := by
  rw [show 458 = 2 * 229 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_229]
  try norm_num

theorem phi_459 : Nat.totient 459 = 288 := by
  rw [show 459 = 3 * 153 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_153]
  try norm_num

theorem phi_460 : Nat.totient 460 = 176 := by
  rw [show 460 = 2 * 230 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_230]
  try norm_num

theorem phi_461 : Nat.totient 461 = 460 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_462 : Nat.totient 462 = 120 := by
  rw [show 462 = 2 * 231 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_231]
  try norm_num

theorem phi_463 : Nat.totient 463 = 462 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_464 : Nat.totient 464 = 224 := by
  rw [show 464 = 2 * 232 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_232]
  try norm_num

theorem phi_465 : Nat.totient 465 = 240 := by
  rw [show 465 = 3 * 155 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_155]
  try norm_num

theorem phi_466 : Nat.totient 466 = 232 := by
  rw [show 466 = 2 * 233 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_233]
  try norm_num

theorem phi_467 : Nat.totient 467 = 466 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_468 : Nat.totient 468 = 144 := by
  rw [show 468 = 2 * 234 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_234]
  try norm_num

theorem phi_469 : Nat.totient 469 = 396 := by
  rw [show 469 = 7 * 67 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_67]
  try norm_num

theorem phi_470 : Nat.totient 470 = 184 := by
  rw [show 470 = 2 * 235 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_235]
  try norm_num

theorem phi_471 : Nat.totient 471 = 312 := by
  rw [show 471 = 3 * 157 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_157]
  try norm_num

theorem phi_472 : Nat.totient 472 = 232 := by
  rw [show 472 = 2 * 236 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_236]
  try norm_num

theorem phi_473 : Nat.totient 473 = 420 := by
  rw [show 473 = 11 * 43 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_43]
  try norm_num

theorem phi_474 : Nat.totient 474 = 156 := by
  rw [show 474 = 2 * 237 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_237]
  try norm_num

theorem phi_475 : Nat.totient 475 = 360 := by
  rw [show 475 = 5 * 95 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_95]
  try norm_num

theorem phi_476 : Nat.totient 476 = 192 := by
  rw [show 476 = 2 * 238 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_238]
  try norm_num

theorem phi_477 : Nat.totient 477 = 312 := by
  rw [show 477 = 3 * 159 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_159]
  try norm_num

theorem phi_478 : Nat.totient 478 = 238 := by
  rw [show 478 = 2 * 239 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_239]
  try norm_num

theorem phi_479 : Nat.totient 479 = 478 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_480 : Nat.totient 480 = 128 := by
  rw [show 480 = 2 * 240 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_240]
  try norm_num

theorem phi_481 : Nat.totient 481 = 432 := by
  rw [show 481 = 13 * 37 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_37]
  try norm_num

theorem phi_482 : Nat.totient 482 = 240 := by
  rw [show 482 = 2 * 241 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_241]
  try norm_num

theorem phi_483 : Nat.totient 483 = 264 := by
  rw [show 483 = 3 * 161 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_161]
  try norm_num

theorem phi_484 : Nat.totient 484 = 220 := by
  rw [show 484 = 2 * 242 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_242]
  try norm_num

theorem phi_485 : Nat.totient 485 = 384 := by
  rw [show 485 = 5 * 97 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_97]
  try norm_num

theorem phi_486 : Nat.totient 486 = 162 := by
  rw [show 486 = 2 * 243 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_243]
  try norm_num

theorem phi_487 : Nat.totient 487 = 486 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_488 : Nat.totient 488 = 240 := by
  rw [show 488 = 2 * 244 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_244]
  try norm_num

theorem phi_489 : Nat.totient 489 = 324 := by
  rw [show 489 = 3 * 163 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_163]
  try norm_num

theorem phi_490 : Nat.totient 490 = 168 := by
  rw [show 490 = 2 * 245 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_245]
  try norm_num

theorem phi_491 : Nat.totient 491 = 490 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_492 : Nat.totient 492 = 160 := by
  rw [show 492 = 2 * 246 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_246]
  try norm_num

theorem phi_493 : Nat.totient 493 = 448 := by
  rw [show 493 = 17 * 29 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_29]
  try norm_num

theorem phi_494 : Nat.totient 494 = 216 := by
  rw [show 494 = 2 * 247 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_247]
  try norm_num

theorem phi_495 : Nat.totient 495 = 240 := by
  rw [show 495 = 3 * 165 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_165]
  try norm_num

theorem phi_496 : Nat.totient 496 = 240 := by
  rw [show 496 = 2 * 248 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_248]
  try norm_num

theorem phi_497 : Nat.totient 497 = 420 := by
  rw [show 497 = 7 * 71 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_71]
  try norm_num

theorem phi_498 : Nat.totient 498 = 164 := by
  rw [show 498 = 2 * 249 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_249]
  try norm_num

theorem phi_499 : Nat.totient 499 = 498 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_500 : Nat.totient 500 = 200 := by
  rw [show 500 = 2 * 250 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_250]
  try norm_num

theorem phi_501 : Nat.totient 501 = 332 := by
  rw [show 501 = 3 * 167 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_167]
  try norm_num

theorem phi_502 : Nat.totient 502 = 250 := by
  rw [show 502 = 2 * 251 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_251]
  try norm_num

theorem phi_503 : Nat.totient 503 = 502 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_504 : Nat.totient 504 = 144 := by
  rw [show 504 = 2 * 252 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_252]
  try norm_num

theorem phi_505 : Nat.totient 505 = 400 := by
  rw [show 505 = 5 * 101 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_101]
  try norm_num

theorem phi_506 : Nat.totient 506 = 220 := by
  rw [show 506 = 2 * 253 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_253]
  try norm_num

theorem phi_507 : Nat.totient 507 = 312 := by
  rw [show 507 = 3 * 169 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_169]
  try norm_num

theorem phi_508 : Nat.totient 508 = 252 := by
  rw [show 508 = 2 * 254 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_254]
  try norm_num

theorem phi_509 : Nat.totient 509 = 508 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_510 : Nat.totient 510 = 128 := by
  rw [show 510 = 2 * 255 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_255]
  try norm_num

theorem phi_511 : Nat.totient 511 = 432 := by
  rw [show 511 = 7 * 73 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_73]
  try norm_num

theorem phi_512 : Nat.totient 512 = 256 := by
  rw [show 512 = 2 * 256 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_256]
  try norm_num

theorem phi_513 : Nat.totient 513 = 324 := by
  rw [show 513 = 3 * 171 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_171]
  try norm_num

theorem phi_514 : Nat.totient 514 = 256 := by
  rw [show 514 = 2 * 257 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_257]
  try norm_num

theorem phi_515 : Nat.totient 515 = 408 := by
  rw [show 515 = 5 * 103 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_103]
  try norm_num

theorem phi_516 : Nat.totient 516 = 168 := by
  rw [show 516 = 2 * 258 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_258]
  try norm_num

theorem phi_517 : Nat.totient 517 = 460 := by
  rw [show 517 = 11 * 47 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_47]
  try norm_num

theorem phi_518 : Nat.totient 518 = 216 := by
  rw [show 518 = 2 * 259 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_259]
  try norm_num

theorem phi_519 : Nat.totient 519 = 344 := by
  rw [show 519 = 3 * 173 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_173]
  try norm_num

theorem phi_520 : Nat.totient 520 = 192 := by
  rw [show 520 = 2 * 260 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_260]
  try norm_num

theorem phi_521 : Nat.totient 521 = 520 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_522 : Nat.totient 522 = 168 := by
  rw [show 522 = 2 * 261 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_261]
  try norm_num

theorem phi_523 : Nat.totient 523 = 522 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_524 : Nat.totient 524 = 260 := by
  rw [show 524 = 2 * 262 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_262]
  try norm_num

theorem phi_525 : Nat.totient 525 = 240 := by
  rw [show 525 = 3 * 175 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_175]
  try norm_num

theorem phi_526 : Nat.totient 526 = 262 := by
  rw [show 526 = 2 * 263 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_263]
  try norm_num

theorem phi_527 : Nat.totient 527 = 480 := by
  rw [show 527 = 17 * 31 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_31]
  try norm_num

theorem phi_528 : Nat.totient 528 = 160 := by
  rw [show 528 = 2 * 264 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_264]
  try norm_num

theorem phi_529 : Nat.totient 529 = 506 := by
  rw [show 529 = 23 * 23 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_23]
  try norm_num

theorem phi_530 : Nat.totient 530 = 208 := by
  rw [show 530 = 2 * 265 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_265]
  try norm_num

theorem phi_531 : Nat.totient 531 = 348 := by
  rw [show 531 = 3 * 177 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_177]
  try norm_num

theorem phi_532 : Nat.totient 532 = 216 := by
  rw [show 532 = 2 * 266 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_266]
  try norm_num

theorem phi_533 : Nat.totient 533 = 480 := by
  rw [show 533 = 13 * 41 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_41]
  try norm_num

theorem phi_534 : Nat.totient 534 = 176 := by
  rw [show 534 = 2 * 267 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_267]
  try norm_num

theorem phi_535 : Nat.totient 535 = 424 := by
  rw [show 535 = 5 * 107 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_107]
  try norm_num

theorem phi_536 : Nat.totient 536 = 264 := by
  rw [show 536 = 2 * 268 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_268]
  try norm_num

theorem phi_537 : Nat.totient 537 = 356 := by
  rw [show 537 = 3 * 179 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_179]
  try norm_num

theorem phi_538 : Nat.totient 538 = 268 := by
  rw [show 538 = 2 * 269 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_269]
  try norm_num

theorem phi_539 : Nat.totient 539 = 420 := by
  rw [show 539 = 7 * 77 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_77]
  try norm_num

theorem phi_540 : Nat.totient 540 = 144 := by
  rw [show 540 = 2 * 270 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_270]
  try norm_num

theorem phi_541 : Nat.totient 541 = 540 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_542 : Nat.totient 542 = 270 := by
  rw [show 542 = 2 * 271 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_271]
  try norm_num

theorem phi_543 : Nat.totient 543 = 360 := by
  rw [show 543 = 3 * 181 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_181]
  try norm_num

theorem phi_544 : Nat.totient 544 = 256 := by
  rw [show 544 = 2 * 272 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_272]
  try norm_num

theorem phi_545 : Nat.totient 545 = 432 := by
  rw [show 545 = 5 * 109 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_109]
  try norm_num

theorem phi_546 : Nat.totient 546 = 144 := by
  rw [show 546 = 2 * 273 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_273]
  try norm_num

theorem phi_547 : Nat.totient 547 = 546 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_548 : Nat.totient 548 = 272 := by
  rw [show 548 = 2 * 274 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_274]
  try norm_num

theorem phi_549 : Nat.totient 549 = 360 := by
  rw [show 549 = 3 * 183 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_183]
  try norm_num

theorem phi_550 : Nat.totient 550 = 200 := by
  rw [show 550 = 2 * 275 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_275]
  try norm_num

theorem phi_551 : Nat.totient 551 = 504 := by
  rw [show 551 = 19 * 29 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_29]
  try norm_num

theorem phi_552 : Nat.totient 552 = 176 := by
  rw [show 552 = 2 * 276 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_276]
  try norm_num

theorem phi_553 : Nat.totient 553 = 468 := by
  rw [show 553 = 7 * 79 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_79]
  try norm_num

theorem phi_554 : Nat.totient 554 = 276 := by
  rw [show 554 = 2 * 277 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_277]
  try norm_num

theorem phi_555 : Nat.totient 555 = 288 := by
  rw [show 555 = 3 * 185 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_185]
  try norm_num

theorem phi_556 : Nat.totient 556 = 276 := by
  rw [show 556 = 2 * 278 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_278]
  try norm_num

theorem phi_557 : Nat.totient 557 = 556 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_558 : Nat.totient 558 = 180 := by
  rw [show 558 = 2 * 279 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_279]
  try norm_num

theorem phi_559 : Nat.totient 559 = 504 := by
  rw [show 559 = 13 * 43 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_43]
  try norm_num

theorem phi_560 : Nat.totient 560 = 192 := by
  rw [show 560 = 2 * 280 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_280]
  try norm_num

theorem phi_561 : Nat.totient 561 = 320 := by
  rw [show 561 = 3 * 187 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_187]
  try norm_num

theorem phi_562 : Nat.totient 562 = 280 := by
  rw [show 562 = 2 * 281 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_281]
  try norm_num

theorem phi_563 : Nat.totient 563 = 562 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_564 : Nat.totient 564 = 184 := by
  rw [show 564 = 2 * 282 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_282]
  try norm_num

theorem phi_565 : Nat.totient 565 = 448 := by
  rw [show 565 = 5 * 113 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_113]
  try norm_num

theorem phi_566 : Nat.totient 566 = 282 := by
  rw [show 566 = 2 * 283 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_283]
  try norm_num

theorem phi_567 : Nat.totient 567 = 324 := by
  rw [show 567 = 3 * 189 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_189]
  try norm_num

theorem phi_568 : Nat.totient 568 = 280 := by
  rw [show 568 = 2 * 284 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_284]
  try norm_num

theorem phi_569 : Nat.totient 569 = 568 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_570 : Nat.totient 570 = 144 := by
  rw [show 570 = 2 * 285 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_285]
  try norm_num

theorem phi_571 : Nat.totient 571 = 570 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_572 : Nat.totient 572 = 240 := by
  rw [show 572 = 2 * 286 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_286]
  try norm_num

theorem phi_573 : Nat.totient 573 = 380 := by
  rw [show 573 = 3 * 191 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_191]
  try norm_num

theorem phi_574 : Nat.totient 574 = 240 := by
  rw [show 574 = 2 * 287 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_287]
  try norm_num

theorem phi_575 : Nat.totient 575 = 440 := by
  rw [show 575 = 5 * 115 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_115]
  try norm_num

theorem phi_576 : Nat.totient 576 = 192 := by
  rw [show 576 = 2 * 288 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_288]
  try norm_num

theorem phi_577 : Nat.totient 577 = 576 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_578 : Nat.totient 578 = 272 := by
  rw [show 578 = 2 * 289 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_289]
  try norm_num

theorem phi_579 : Nat.totient 579 = 384 := by
  rw [show 579 = 3 * 193 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_193]
  try norm_num

theorem phi_580 : Nat.totient 580 = 224 := by
  rw [show 580 = 2 * 290 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_290]
  try norm_num

theorem phi_581 : Nat.totient 581 = 492 := by
  rw [show 581 = 7 * 83 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_83]
  try norm_num

theorem phi_582 : Nat.totient 582 = 192 := by
  rw [show 582 = 2 * 291 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_291]
  try norm_num

theorem phi_583 : Nat.totient 583 = 520 := by
  rw [show 583 = 11 * 53 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_53]
  try norm_num

theorem phi_584 : Nat.totient 584 = 288 := by
  rw [show 584 = 2 * 292 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_292]
  try norm_num

theorem phi_585 : Nat.totient 585 = 288 := by
  rw [show 585 = 3 * 195 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_195]
  try norm_num

theorem phi_586 : Nat.totient 586 = 292 := by
  rw [show 586 = 2 * 293 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_293]
  try norm_num

theorem phi_587 : Nat.totient 587 = 586 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_588 : Nat.totient 588 = 168 := by
  rw [show 588 = 2 * 294 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_294]
  try norm_num

theorem phi_589 : Nat.totient 589 = 540 := by
  rw [show 589 = 19 * 31 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_31]
  try norm_num

theorem phi_590 : Nat.totient 590 = 232 := by
  rw [show 590 = 2 * 295 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_295]
  try norm_num

theorem phi_591 : Nat.totient 591 = 392 := by
  rw [show 591 = 3 * 197 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_197]
  try norm_num

theorem phi_592 : Nat.totient 592 = 288 := by
  rw [show 592 = 2 * 296 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_296]
  try norm_num

theorem phi_593 : Nat.totient 593 = 592 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_594 : Nat.totient 594 = 180 := by
  rw [show 594 = 2 * 297 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_297]
  try norm_num

theorem phi_595 : Nat.totient 595 = 384 := by
  rw [show 595 = 5 * 119 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_119]
  try norm_num

theorem phi_596 : Nat.totient 596 = 296 := by
  rw [show 596 = 2 * 298 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_298]
  try norm_num

theorem phi_597 : Nat.totient 597 = 396 := by
  rw [show 597 = 3 * 199 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_199]
  try norm_num

theorem phi_598 : Nat.totient 598 = 264 := by
  rw [show 598 = 2 * 299 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_299]
  try norm_num

theorem phi_599 : Nat.totient 599 = 598 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_600 : Nat.totient 600 = 160 := by
  rw [show 600 = 2 * 300 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_300]
  try norm_num

theorem phi_601 : Nat.totient 601 = 600 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_602 : Nat.totient 602 = 252 := by
  rw [show 602 = 2 * 301 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_301]
  try norm_num

theorem phi_603 : Nat.totient 603 = 396 := by
  rw [show 603 = 3 * 201 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_201]
  try norm_num

theorem phi_604 : Nat.totient 604 = 300 := by
  rw [show 604 = 2 * 302 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_302]
  try norm_num

theorem phi_605 : Nat.totient 605 = 440 := by
  rw [show 605 = 5 * 121 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_121]
  try norm_num

theorem phi_606 : Nat.totient 606 = 200 := by
  rw [show 606 = 2 * 303 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_303]
  try norm_num

theorem phi_607 : Nat.totient 607 = 606 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_608 : Nat.totient 608 = 288 := by
  rw [show 608 = 2 * 304 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_304]
  try norm_num

theorem phi_609 : Nat.totient 609 = 336 := by
  rw [show 609 = 3 * 203 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_203]
  try norm_num

theorem phi_610 : Nat.totient 610 = 240 := by
  rw [show 610 = 2 * 305 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_305]
  try norm_num

theorem phi_611 : Nat.totient 611 = 552 := by
  rw [show 611 = 13 * 47 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_47]
  try norm_num

theorem phi_612 : Nat.totient 612 = 192 := by
  rw [show 612 = 2 * 306 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_306]
  try norm_num

theorem phi_613 : Nat.totient 613 = 612 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_614 : Nat.totient 614 = 306 := by
  rw [show 614 = 2 * 307 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_307]
  try norm_num

theorem phi_615 : Nat.totient 615 = 320 := by
  rw [show 615 = 3 * 205 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_205]
  try norm_num

theorem phi_616 : Nat.totient 616 = 240 := by
  rw [show 616 = 2 * 308 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_308]
  try norm_num

theorem phi_617 : Nat.totient 617 = 616 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_618 : Nat.totient 618 = 204 := by
  rw [show 618 = 2 * 309 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_309]
  try norm_num

theorem phi_619 : Nat.totient 619 = 618 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_620 : Nat.totient 620 = 240 := by
  rw [show 620 = 2 * 310 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_310]
  try norm_num

theorem phi_621 : Nat.totient 621 = 396 := by
  rw [show 621 = 3 * 207 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_207]
  try norm_num

theorem phi_622 : Nat.totient 622 = 310 := by
  rw [show 622 = 2 * 311 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_311]
  try norm_num

theorem phi_623 : Nat.totient 623 = 528 := by
  rw [show 623 = 7 * 89 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_89]
  try norm_num

theorem phi_624 : Nat.totient 624 = 192 := by
  rw [show 624 = 2 * 312 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_312]
  try norm_num

theorem phi_625 : Nat.totient 625 = 500 := by
  rw [show 625 = 5 * 125 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_125]
  try norm_num

theorem phi_626 : Nat.totient 626 = 312 := by
  rw [show 626 = 2 * 313 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_313]
  try norm_num

theorem phi_627 : Nat.totient 627 = 360 := by
  rw [show 627 = 3 * 209 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_209]
  try norm_num

theorem phi_628 : Nat.totient 628 = 312 := by
  rw [show 628 = 2 * 314 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_314]
  try norm_num

theorem phi_629 : Nat.totient 629 = 576 := by
  rw [show 629 = 17 * 37 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_37]
  try norm_num

theorem phi_630 : Nat.totient 630 = 144 := by
  rw [show 630 = 2 * 315 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_315]
  try norm_num

theorem phi_631 : Nat.totient 631 = 630 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_632 : Nat.totient 632 = 312 := by
  rw [show 632 = 2 * 316 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_316]
  try norm_num

theorem phi_633 : Nat.totient 633 = 420 := by
  rw [show 633 = 3 * 211 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_211]
  try norm_num

theorem phi_634 : Nat.totient 634 = 316 := by
  rw [show 634 = 2 * 317 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_317]
  try norm_num

theorem phi_635 : Nat.totient 635 = 504 := by
  rw [show 635 = 5 * 127 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_127]
  try norm_num

theorem phi_636 : Nat.totient 636 = 208 := by
  rw [show 636 = 2 * 318 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_318]
  try norm_num

theorem phi_637 : Nat.totient 637 = 504 := by
  rw [show 637 = 7 * 91 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_91]
  try norm_num

theorem phi_638 : Nat.totient 638 = 280 := by
  rw [show 638 = 2 * 319 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_319]
  try norm_num

theorem phi_639 : Nat.totient 639 = 420 := by
  rw [show 639 = 3 * 213 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_213]
  try norm_num

theorem phi_640 : Nat.totient 640 = 256 := by
  rw [show 640 = 2 * 320 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_320]
  try norm_num

theorem phi_641 : Nat.totient 641 = 640 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_642 : Nat.totient 642 = 212 := by
  rw [show 642 = 2 * 321 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_321]
  try norm_num

theorem phi_643 : Nat.totient 643 = 642 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_644 : Nat.totient 644 = 264 := by
  rw [show 644 = 2 * 322 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_322]
  try norm_num

theorem phi_645 : Nat.totient 645 = 336 := by
  rw [show 645 = 3 * 215 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_215]
  try norm_num

theorem phi_646 : Nat.totient 646 = 288 := by
  rw [show 646 = 2 * 323 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_323]
  try norm_num

theorem phi_647 : Nat.totient 647 = 646 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_648 : Nat.totient 648 = 216 := by
  rw [show 648 = 2 * 324 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_324]
  try norm_num

theorem phi_649 : Nat.totient 649 = 580 := by
  rw [show 649 = 11 * 59 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_59]
  try norm_num

theorem phi_650 : Nat.totient 650 = 240 := by
  rw [show 650 = 2 * 325 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_325]
  try norm_num

theorem phi_651 : Nat.totient 651 = 360 := by
  rw [show 651 = 3 * 217 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_217]
  try norm_num

theorem phi_652 : Nat.totient 652 = 324 := by
  rw [show 652 = 2 * 326 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_326]
  try norm_num

theorem phi_653 : Nat.totient 653 = 652 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_654 : Nat.totient 654 = 216 := by
  rw [show 654 = 2 * 327 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_327]
  try norm_num

theorem phi_655 : Nat.totient 655 = 520 := by
  rw [show 655 = 5 * 131 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_131]
  try norm_num

theorem phi_656 : Nat.totient 656 = 320 := by
  rw [show 656 = 2 * 328 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_328]
  try norm_num

theorem phi_657 : Nat.totient 657 = 432 := by
  rw [show 657 = 3 * 219 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_219]
  try norm_num

theorem phi_658 : Nat.totient 658 = 276 := by
  rw [show 658 = 2 * 329 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_329]
  try norm_num

theorem phi_659 : Nat.totient 659 = 658 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_660 : Nat.totient 660 = 160 := by
  rw [show 660 = 2 * 330 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_330]
  try norm_num

theorem phi_661 : Nat.totient 661 = 660 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_662 : Nat.totient 662 = 330 := by
  rw [show 662 = 2 * 331 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_331]
  try norm_num

theorem phi_663 : Nat.totient 663 = 384 := by
  rw [show 663 = 3 * 221 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_221]
  try norm_num

theorem phi_664 : Nat.totient 664 = 328 := by
  rw [show 664 = 2 * 332 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_332]
  try norm_num

theorem phi_665 : Nat.totient 665 = 432 := by
  rw [show 665 = 5 * 133 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_133]
  try norm_num

theorem phi_666 : Nat.totient 666 = 216 := by
  rw [show 666 = 2 * 333 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_333]
  try norm_num

theorem phi_667 : Nat.totient 667 = 616 := by
  rw [show 667 = 23 * 29 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_29]
  try norm_num

theorem phi_668 : Nat.totient 668 = 332 := by
  rw [show 668 = 2 * 334 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_334]
  try norm_num

theorem phi_669 : Nat.totient 669 = 444 := by
  rw [show 669 = 3 * 223 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_223]
  try norm_num

theorem phi_670 : Nat.totient 670 = 264 := by
  rw [show 670 = 2 * 335 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_335]
  try norm_num

theorem phi_671 : Nat.totient 671 = 600 := by
  rw [show 671 = 11 * 61 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_61]
  try norm_num

theorem phi_672 : Nat.totient 672 = 192 := by
  rw [show 672 = 2 * 336 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_336]
  try norm_num

theorem phi_673 : Nat.totient 673 = 672 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_674 : Nat.totient 674 = 336 := by
  rw [show 674 = 2 * 337 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_337]
  try norm_num

theorem phi_675 : Nat.totient 675 = 360 := by
  rw [show 675 = 3 * 225 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_225]
  try norm_num

theorem phi_676 : Nat.totient 676 = 312 := by
  rw [show 676 = 2 * 338 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_338]
  try norm_num

theorem phi_677 : Nat.totient 677 = 676 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_678 : Nat.totient 678 = 224 := by
  rw [show 678 = 2 * 339 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_339]
  try norm_num

theorem phi_679 : Nat.totient 679 = 576 := by
  rw [show 679 = 7 * 97 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_97]
  try norm_num

theorem phi_680 : Nat.totient 680 = 256 := by
  rw [show 680 = 2 * 340 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_340]
  try norm_num

theorem phi_681 : Nat.totient 681 = 452 := by
  rw [show 681 = 3 * 227 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_227]
  try norm_num

theorem phi_682 : Nat.totient 682 = 300 := by
  rw [show 682 = 2 * 341 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_341]
  try norm_num

theorem phi_683 : Nat.totient 683 = 682 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_684 : Nat.totient 684 = 216 := by
  rw [show 684 = 2 * 342 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_342]
  try norm_num

theorem phi_685 : Nat.totient 685 = 544 := by
  rw [show 685 = 5 * 137 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_137]
  try norm_num

theorem phi_686 : Nat.totient 686 = 294 := by
  rw [show 686 = 2 * 343 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_343]
  try norm_num

theorem phi_687 : Nat.totient 687 = 456 := by
  rw [show 687 = 3 * 229 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_229]
  try norm_num

theorem phi_688 : Nat.totient 688 = 336 := by
  rw [show 688 = 2 * 344 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_344]
  try norm_num

theorem phi_689 : Nat.totient 689 = 624 := by
  rw [show 689 = 13 * 53 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_53]
  try norm_num

theorem phi_690 : Nat.totient 690 = 176 := by
  rw [show 690 = 2 * 345 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_345]
  try norm_num

theorem phi_691 : Nat.totient 691 = 690 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_692 : Nat.totient 692 = 344 := by
  rw [show 692 = 2 * 346 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_346]
  try norm_num

theorem phi_693 : Nat.totient 693 = 360 := by
  rw [show 693 = 3 * 231 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_231]
  try norm_num

theorem phi_694 : Nat.totient 694 = 346 := by
  rw [show 694 = 2 * 347 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_347]
  try norm_num

theorem phi_695 : Nat.totient 695 = 552 := by
  rw [show 695 = 5 * 139 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_139]
  try norm_num

theorem phi_696 : Nat.totient 696 = 224 := by
  rw [show 696 = 2 * 348 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_348]
  try norm_num

theorem phi_697 : Nat.totient 697 = 640 := by
  rw [show 697 = 17 * 41 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_41]
  try norm_num

theorem phi_698 : Nat.totient 698 = 348 := by
  rw [show 698 = 2 * 349 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_349]
  try norm_num

theorem phi_699 : Nat.totient 699 = 464 := by
  rw [show 699 = 3 * 233 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_233]
  try norm_num

theorem phi_700 : Nat.totient 700 = 240 := by
  rw [show 700 = 2 * 350 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_350]
  try norm_num

theorem phi_701 : Nat.totient 701 = 700 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_702 : Nat.totient 702 = 216 := by
  rw [show 702 = 2 * 351 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_351]
  try norm_num

theorem phi_703 : Nat.totient 703 = 648 := by
  rw [show 703 = 19 * 37 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_37]
  try norm_num

theorem phi_704 : Nat.totient 704 = 320 := by
  rw [show 704 = 2 * 352 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_352]
  try norm_num

theorem phi_705 : Nat.totient 705 = 368 := by
  rw [show 705 = 3 * 235 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_235]
  try norm_num

theorem phi_706 : Nat.totient 706 = 352 := by
  rw [show 706 = 2 * 353 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_353]
  try norm_num

theorem phi_707 : Nat.totient 707 = 600 := by
  rw [show 707 = 7 * 101 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_101]
  try norm_num

theorem phi_708 : Nat.totient 708 = 232 := by
  rw [show 708 = 2 * 354 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_354]
  try norm_num

theorem phi_709 : Nat.totient 709 = 708 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_710 : Nat.totient 710 = 280 := by
  rw [show 710 = 2 * 355 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_355]
  try norm_num

theorem phi_711 : Nat.totient 711 = 468 := by
  rw [show 711 = 3 * 237 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_237]
  try norm_num

theorem phi_712 : Nat.totient 712 = 352 := by
  rw [show 712 = 2 * 356 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_356]
  try norm_num

theorem phi_713 : Nat.totient 713 = 660 := by
  rw [show 713 = 23 * 31 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_31]
  try norm_num

theorem phi_714 : Nat.totient 714 = 192 := by
  rw [show 714 = 2 * 357 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_357]
  try norm_num

theorem phi_715 : Nat.totient 715 = 480 := by
  rw [show 715 = 5 * 143 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_143]
  try norm_num

theorem phi_716 : Nat.totient 716 = 356 := by
  rw [show 716 = 2 * 358 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_358]
  try norm_num

theorem phi_717 : Nat.totient 717 = 476 := by
  rw [show 717 = 3 * 239 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_239]
  try norm_num

theorem phi_718 : Nat.totient 718 = 358 := by
  rw [show 718 = 2 * 359 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_359]
  try norm_num

theorem phi_719 : Nat.totient 719 = 718 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_720 : Nat.totient 720 = 192 := by
  rw [show 720 = 2 * 360 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_360]
  try norm_num

theorem phi_721 : Nat.totient 721 = 612 := by
  rw [show 721 = 7 * 103 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_103]
  try norm_num

theorem phi_722 : Nat.totient 722 = 342 := by
  rw [show 722 = 2 * 361 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_361]
  try norm_num

theorem phi_723 : Nat.totient 723 = 480 := by
  rw [show 723 = 3 * 241 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_241]
  try norm_num

theorem phi_724 : Nat.totient 724 = 360 := by
  rw [show 724 = 2 * 362 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_362]
  try norm_num

theorem phi_725 : Nat.totient 725 = 560 := by
  rw [show 725 = 5 * 145 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_145]
  try norm_num

theorem phi_726 : Nat.totient 726 = 220 := by
  rw [show 726 = 2 * 363 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_363]
  try norm_num

theorem phi_727 : Nat.totient 727 = 726 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_728 : Nat.totient 728 = 288 := by
  rw [show 728 = 2 * 364 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_364]
  try norm_num

theorem phi_729 : Nat.totient 729 = 486 := by
  rw [show 729 = 3 * 243 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_243]
  try norm_num

theorem phi_730 : Nat.totient 730 = 288 := by
  rw [show 730 = 2 * 365 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_365]
  try norm_num

theorem phi_731 : Nat.totient 731 = 672 := by
  rw [show 731 = 17 * 43 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_43]
  try norm_num

theorem phi_732 : Nat.totient 732 = 240 := by
  rw [show 732 = 2 * 366 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_366]
  try norm_num

theorem phi_733 : Nat.totient 733 = 732 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_734 : Nat.totient 734 = 366 := by
  rw [show 734 = 2 * 367 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_367]
  try norm_num

theorem phi_735 : Nat.totient 735 = 336 := by
  rw [show 735 = 3 * 245 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_245]
  try norm_num

theorem phi_736 : Nat.totient 736 = 352 := by
  rw [show 736 = 2 * 368 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_368]
  try norm_num

theorem phi_737 : Nat.totient 737 = 660 := by
  rw [show 737 = 11 * 67 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_67]
  try norm_num

theorem phi_738 : Nat.totient 738 = 240 := by
  rw [show 738 = 2 * 369 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_369]
  try norm_num

theorem phi_739 : Nat.totient 739 = 738 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_740 : Nat.totient 740 = 288 := by
  rw [show 740 = 2 * 370 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_370]
  try norm_num

theorem phi_741 : Nat.totient 741 = 432 := by
  rw [show 741 = 3 * 247 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_247]
  try norm_num

theorem phi_742 : Nat.totient 742 = 312 := by
  rw [show 742 = 2 * 371 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_371]
  try norm_num

theorem phi_743 : Nat.totient 743 = 742 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_744 : Nat.totient 744 = 240 := by
  rw [show 744 = 2 * 372 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_372]
  try norm_num

theorem phi_745 : Nat.totient 745 = 592 := by
  rw [show 745 = 5 * 149 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_149]
  try norm_num

theorem phi_746 : Nat.totient 746 = 372 := by
  rw [show 746 = 2 * 373 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_373]
  try norm_num

theorem phi_747 : Nat.totient 747 = 492 := by
  rw [show 747 = 3 * 249 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_249]
  try norm_num

theorem phi_748 : Nat.totient 748 = 320 := by
  rw [show 748 = 2 * 374 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_374]
  try norm_num

theorem phi_749 : Nat.totient 749 = 636 := by
  rw [show 749 = 7 * 107 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_107]
  try norm_num

theorem phi_750 : Nat.totient 750 = 200 := by
  rw [show 750 = 2 * 375 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_375]
  try norm_num

theorem phi_751 : Nat.totient 751 = 750 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_752 : Nat.totient 752 = 368 := by
  rw [show 752 = 2 * 376 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_376]
  try norm_num

theorem phi_753 : Nat.totient 753 = 500 := by
  rw [show 753 = 3 * 251 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_251]
  try norm_num

theorem phi_754 : Nat.totient 754 = 336 := by
  rw [show 754 = 2 * 377 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_377]
  try norm_num

theorem phi_755 : Nat.totient 755 = 600 := by
  rw [show 755 = 5 * 151 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_151]
  try norm_num

theorem phi_756 : Nat.totient 756 = 216 := by
  rw [show 756 = 2 * 378 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_378]
  try norm_num

theorem phi_757 : Nat.totient 757 = 756 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_758 : Nat.totient 758 = 378 := by
  rw [show 758 = 2 * 379 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_379]
  try norm_num

theorem phi_759 : Nat.totient 759 = 440 := by
  rw [show 759 = 3 * 253 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_253]
  try norm_num

theorem phi_760 : Nat.totient 760 = 288 := by
  rw [show 760 = 2 * 380 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_380]
  try norm_num

theorem phi_761 : Nat.totient 761 = 760 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_762 : Nat.totient 762 = 252 := by
  rw [show 762 = 2 * 381 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_381]
  try norm_num

theorem phi_763 : Nat.totient 763 = 648 := by
  rw [show 763 = 7 * 109 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_109]
  try norm_num

theorem phi_764 : Nat.totient 764 = 380 := by
  rw [show 764 = 2 * 382 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_382]
  try norm_num

theorem phi_765 : Nat.totient 765 = 384 := by
  rw [show 765 = 3 * 255 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_255]
  try norm_num

theorem phi_766 : Nat.totient 766 = 382 := by
  rw [show 766 = 2 * 383 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_383]
  try norm_num

theorem phi_767 : Nat.totient 767 = 696 := by
  rw [show 767 = 13 * 59 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_59]
  try norm_num

theorem phi_768 : Nat.totient 768 = 256 := by
  rw [show 768 = 2 * 384 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_384]
  try norm_num

theorem phi_769 : Nat.totient 769 = 768 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_770 : Nat.totient 770 = 240 := by
  rw [show 770 = 2 * 385 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_385]
  try norm_num

theorem phi_771 : Nat.totient 771 = 512 := by
  rw [show 771 = 3 * 257 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_257]
  try norm_num

theorem phi_772 : Nat.totient 772 = 384 := by
  rw [show 772 = 2 * 386 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_386]
  try norm_num

theorem phi_773 : Nat.totient 773 = 772 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_774 : Nat.totient 774 = 252 := by
  rw [show 774 = 2 * 387 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_387]
  try norm_num

theorem phi_775 : Nat.totient 775 = 600 := by
  rw [show 775 = 5 * 155 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_155]
  try norm_num

theorem phi_776 : Nat.totient 776 = 384 := by
  rw [show 776 = 2 * 388 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_388]
  try norm_num

theorem phi_777 : Nat.totient 777 = 432 := by
  rw [show 777 = 3 * 259 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_259]
  try norm_num

theorem phi_778 : Nat.totient 778 = 388 := by
  rw [show 778 = 2 * 389 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_389]
  try norm_num

theorem phi_779 : Nat.totient 779 = 720 := by
  rw [show 779 = 19 * 41 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_41]
  try norm_num

theorem phi_780 : Nat.totient 780 = 192 := by
  rw [show 780 = 2 * 390 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_390]
  try norm_num

theorem phi_781 : Nat.totient 781 = 700 := by
  rw [show 781 = 11 * 71 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_71]
  try norm_num

theorem phi_782 : Nat.totient 782 = 352 := by
  rw [show 782 = 2 * 391 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_391]
  try norm_num

theorem phi_783 : Nat.totient 783 = 504 := by
  rw [show 783 = 3 * 261 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_261]
  try norm_num

theorem phi_784 : Nat.totient 784 = 336 := by
  rw [show 784 = 2 * 392 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_392]
  try norm_num

theorem phi_785 : Nat.totient 785 = 624 := by
  rw [show 785 = 5 * 157 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_157]
  try norm_num

theorem phi_786 : Nat.totient 786 = 260 := by
  rw [show 786 = 2 * 393 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_393]
  try norm_num

theorem phi_787 : Nat.totient 787 = 786 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_788 : Nat.totient 788 = 392 := by
  rw [show 788 = 2 * 394 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_394]
  try norm_num

theorem phi_789 : Nat.totient 789 = 524 := by
  rw [show 789 = 3 * 263 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_263]
  try norm_num

theorem phi_790 : Nat.totient 790 = 312 := by
  rw [show 790 = 2 * 395 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_395]
  try norm_num

theorem phi_791 : Nat.totient 791 = 672 := by
  rw [show 791 = 7 * 113 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_113]
  try norm_num

theorem phi_792 : Nat.totient 792 = 240 := by
  rw [show 792 = 2 * 396 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_396]
  try norm_num

theorem phi_793 : Nat.totient 793 = 720 := by
  rw [show 793 = 13 * 61 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_61]
  try norm_num

theorem phi_794 : Nat.totient 794 = 396 := by
  rw [show 794 = 2 * 397 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_397]
  try norm_num

theorem phi_795 : Nat.totient 795 = 416 := by
  rw [show 795 = 3 * 265 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_265]
  try norm_num

theorem phi_796 : Nat.totient 796 = 396 := by
  rw [show 796 = 2 * 398 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_398]
  try norm_num

theorem phi_797 : Nat.totient 797 = 796 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_798 : Nat.totient 798 = 216 := by
  rw [show 798 = 2 * 399 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_399]
  try norm_num

theorem phi_799 : Nat.totient 799 = 736 := by
  rw [show 799 = 17 * 47 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_47]
  try norm_num

theorem phi_800 : Nat.totient 800 = 320 := by
  rw [show 800 = 2 * 400 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_400]
  try norm_num

theorem phi_801 : Nat.totient 801 = 528 := by
  rw [show 801 = 3 * 267 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_267]
  try norm_num

theorem phi_802 : Nat.totient 802 = 400 := by
  rw [show 802 = 2 * 401 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_401]
  try norm_num

theorem phi_803 : Nat.totient 803 = 720 := by
  rw [show 803 = 11 * 73 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_73]
  try norm_num

theorem phi_804 : Nat.totient 804 = 264 := by
  rw [show 804 = 2 * 402 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_402]
  try norm_num

theorem phi_805 : Nat.totient 805 = 528 := by
  rw [show 805 = 5 * 161 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_161]
  try norm_num

theorem phi_806 : Nat.totient 806 = 360 := by
  rw [show 806 = 2 * 403 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_403]
  try norm_num

theorem phi_807 : Nat.totient 807 = 536 := by
  rw [show 807 = 3 * 269 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_269]
  try norm_num

theorem phi_808 : Nat.totient 808 = 400 := by
  rw [show 808 = 2 * 404 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_404]
  try norm_num

theorem phi_809 : Nat.totient 809 = 808 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_810 : Nat.totient 810 = 216 := by
  rw [show 810 = 2 * 405 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_405]
  try norm_num

theorem phi_811 : Nat.totient 811 = 810 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_812 : Nat.totient 812 = 336 := by
  rw [show 812 = 2 * 406 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_406]
  try norm_num

theorem phi_813 : Nat.totient 813 = 540 := by
  rw [show 813 = 3 * 271 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_271]
  try norm_num

theorem phi_814 : Nat.totient 814 = 360 := by
  rw [show 814 = 2 * 407 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_407]
  try norm_num

theorem phi_815 : Nat.totient 815 = 648 := by
  rw [show 815 = 5 * 163 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_163]
  try norm_num

theorem phi_816 : Nat.totient 816 = 256 := by
  rw [show 816 = 2 * 408 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_408]
  try norm_num

theorem phi_817 : Nat.totient 817 = 756 := by
  rw [show 817 = 19 * 43 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_43]
  try norm_num

theorem phi_818 : Nat.totient 818 = 408 := by
  rw [show 818 = 2 * 409 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_409]
  try norm_num

theorem phi_819 : Nat.totient 819 = 432 := by
  rw [show 819 = 3 * 273 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_273]
  try norm_num

theorem phi_820 : Nat.totient 820 = 320 := by
  rw [show 820 = 2 * 410 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_410]
  try norm_num

theorem phi_821 : Nat.totient 821 = 820 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_822 : Nat.totient 822 = 272 := by
  rw [show 822 = 2 * 411 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_411]
  try norm_num

theorem phi_823 : Nat.totient 823 = 822 := by
  rw [Nat.totient_prime (by norm_num)]
  try norm_num

theorem phi_824 : Nat.totient 824 = 408 := by
  rw [show 824 = 2 * 412 by norm_num, Nat.totient_mul_of_prime_of_dvd (by norm_num) (by norm_num), phi_412]
  try norm_num

theorem phi_825 : Nat.totient 825 = 400 := by
  rw [show 825 = 3 * 275 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_275]
  try norm_num

theorem phi_826 : Nat.totient 826 = 348 := by
  rw [show 826 = 2 * 413 by norm_num, Nat.totient_mul_of_prime_of_not_dvd (by norm_num) (by norm_num), phi_413]
  try norm_num

def values : List Nat := [0, 1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8, 12, 10, 22, 8, 20, 12, 18, 12, 28, 8, 30, 16, 20, 16, 24, 12, 36, 18, 24, 16, 40, 12, 42, 20, 24, 22, 46, 16, 42, 20, 32, 24, 52, 18, 40, 24, 36, 28, 58, 16, 60, 30, 36, 32, 48, 20, 66, 32, 44, 24, 70, 24, 72, 36, 40, 36, 60, 24, 78, 32, 54, 40, 82, 24, 64, 42, 56, 40, 88, 24, 72, 44, 60, 46, 72, 32, 96, 42, 60, 40, 100, 32, 102, 48, 48, 52, 106, 36, 108, 40, 72, 48, 112, 36, 88, 56, 72, 58, 96, 32, 110, 60, 80, 60, 100, 36, 126, 64, 84, 48, 130, 40, 108, 66, 72, 64, 136, 44, 138, 48, 92, 70, 120, 48, 112, 72, 84, 72, 148, 40, 150, 72, 96, 60, 120, 48, 156, 78, 104, 64, 132, 54, 162, 80, 80, 82, 166, 48, 156, 64, 108, 84, 172, 56, 120, 80, 116, 88, 178, 48, 180, 72, 120, 88, 144, 60, 160, 92, 108, 72, 190, 64, 192, 96, 96, 84, 196, 60, 198, 80, 132, 100, 168, 64, 160, 102, 132, 96, 180, 48, 210, 104, 140, 106, 168, 72, 180, 108, 144, 80, 192, 72, 222, 96, 120, 112, 226, 72, 228, 88, 120, 112, 232, 72, 184, 116, 156, 96, 238, 64, 240, 110, 162, 120, 168, 80, 216, 120, 164, 100, 250, 72, 220, 126, 128, 128, 256, 84, 216, 96, 168, 130, 262, 80, 208, 108, 176, 132, 268, 72, 270, 128, 144, 136, 200, 88, 276, 138, 180, 96, 280, 92, 282, 140, 144, 120, 240, 96, 272, 112, 192, 144, 292, 84, 232, 144, 180, 148, 264, 80, 252, 150, 200, 144, 240, 96, 306, 120, 204, 120, 310, 96, 312, 156, 144, 156, 316, 104, 280, 128, 212, 132, 288, 108, 240, 162, 216, 160, 276, 80, 330, 164, 216, 166, 264, 96, 336, 156, 224, 128, 300, 108, 294, 168, 176, 172, 346, 112, 348, 120, 216, 160, 352, 116, 280, 176, 192, 178, 358, 96, 342, 180, 220, 144, 288, 120, 366, 176, 240, 144, 312, 120, 372, 160, 200, 184, 336, 108, 378, 144, 252, 190, 382, 128, 240, 192, 252, 192, 388, 96, 352, 168, 260, 196, 312, 120, 396, 198, 216, 160, 400, 132, 360, 200, 216, 168, 360, 128, 408, 160, 272, 204, 348, 132, 328, 192, 276, 180, 418, 96, 420, 210, 276, 208, 320, 140, 360, 212, 240, 168, 430, 144, 432, 180, 224, 216, 396, 144, 438, 160, 252, 192, 442, 144, 352, 222, 296, 192, 448, 120, 400, 224, 300, 226, 288, 144, 456, 228, 288, 176, 460, 120, 462, 224, 240, 232, 466, 144, 396, 184, 312, 232, 420, 156, 360, 192, 312, 238, 478, 128, 432, 240, 264, 220, 384, 162, 486, 240, 324, 168, 490, 160, 448, 216, 240, 240, 420, 164, 498, 200, 332, 250, 502, 144, 400, 220, 312, 252, 508, 128, 432, 256, 324, 256, 408, 168, 460, 216, 344, 192, 520, 168, 522, 260, 240, 262, 480, 160, 506, 208, 348, 216, 480, 176, 424, 264, 356, 268, 420, 144, 540, 270, 360, 256, 432, 144, 546, 272, 360, 200, 504, 176, 468, 276, 288, 276, 556, 180, 504, 192, 320, 280, 562, 184, 448, 282, 324, 280, 568, 144, 570, 240, 380, 240, 440, 192, 576, 272, 384, 224, 492, 192, 520, 288, 288, 292, 586, 168, 540, 232, 392, 288, 592, 180, 384, 296, 396, 264, 598, 160, 600, 252, 396, 300, 440, 200, 606, 288, 336, 240, 552, 192, 612, 306, 320, 240, 616, 204, 618, 240, 396, 310, 528, 192, 500, 312, 360, 312, 576, 144, 630, 312, 420, 316, 504, 208, 504, 280, 420, 256, 640, 212, 642, 264, 336, 288, 646, 216, 580, 240, 360, 324, 652, 216, 520, 320, 432, 276, 658, 160, 660, 330, 384, 328, 432, 216, 616, 332, 444, 264, 600, 192, 672, 336, 360, 312, 676, 224, 576, 256, 452, 300, 682, 216, 544, 294, 456, 336, 624, 176, 690, 344, 360, 346, 552, 224, 640, 348, 464, 240, 700, 216, 648, 320, 368, 352, 600, 232, 708, 280, 468, 352, 660, 192, 480, 356, 476, 358, 718, 192, 612, 342, 480, 360, 560, 220, 726, 288, 486, 288, 672, 240, 732, 366, 336, 352, 660, 240, 738, 288, 432, 312, 742, 240, 592, 372, 492, 320, 636, 200, 750, 368, 500, 336, 600, 216, 756, 378, 440, 288, 760, 252, 648, 380, 384, 382, 696, 256, 768, 240, 512, 384, 772, 252, 600, 384, 432, 388, 720, 192, 700, 352, 504, 336, 624, 260, 786, 392, 524, 312, 672, 240, 720, 396, 416, 396, 796, 216, 736, 320, 528, 400, 720, 264, 528, 360, 536, 400, 808, 216, 810, 336, 540, 360, 648, 256, 756, 408, 432, 320, 820, 272, 822, 408, 400, 348]

theorem values_eq : (List.range 827).map Nat.totient = values := by
  change [Nat.totient 0, Nat.totient 1, Nat.totient 2, Nat.totient 3, Nat.totient 4, Nat.totient 5, Nat.totient 6, Nat.totient 7, Nat.totient 8, Nat.totient 9, Nat.totient 10, Nat.totient 11, Nat.totient 12, Nat.totient 13, Nat.totient 14, Nat.totient 15, Nat.totient 16, Nat.totient 17, Nat.totient 18, Nat.totient 19, Nat.totient 20, Nat.totient 21, Nat.totient 22, Nat.totient 23, Nat.totient 24, Nat.totient 25, Nat.totient 26, Nat.totient 27, Nat.totient 28, Nat.totient 29, Nat.totient 30, Nat.totient 31, Nat.totient 32, Nat.totient 33, Nat.totient 34, Nat.totient 35, Nat.totient 36, Nat.totient 37, Nat.totient 38, Nat.totient 39, Nat.totient 40, Nat.totient 41, Nat.totient 42, Nat.totient 43, Nat.totient 44, Nat.totient 45, Nat.totient 46, Nat.totient 47, Nat.totient 48, Nat.totient 49, Nat.totient 50, Nat.totient 51, Nat.totient 52, Nat.totient 53, Nat.totient 54, Nat.totient 55, Nat.totient 56, Nat.totient 57, Nat.totient 58, Nat.totient 59, Nat.totient 60, Nat.totient 61, Nat.totient 62, Nat.totient 63, Nat.totient 64, Nat.totient 65, Nat.totient 66, Nat.totient 67, Nat.totient 68, Nat.totient 69, Nat.totient 70, Nat.totient 71, Nat.totient 72, Nat.totient 73, Nat.totient 74, Nat.totient 75, Nat.totient 76, Nat.totient 77, Nat.totient 78, Nat.totient 79, Nat.totient 80, Nat.totient 81, Nat.totient 82, Nat.totient 83, Nat.totient 84, Nat.totient 85, Nat.totient 86, Nat.totient 87, Nat.totient 88, Nat.totient 89, Nat.totient 90, Nat.totient 91, Nat.totient 92, Nat.totient 93, Nat.totient 94, Nat.totient 95, Nat.totient 96, Nat.totient 97, Nat.totient 98, Nat.totient 99, Nat.totient 100, Nat.totient 101, Nat.totient 102, Nat.totient 103, Nat.totient 104, Nat.totient 105, Nat.totient 106, Nat.totient 107, Nat.totient 108, Nat.totient 109, Nat.totient 110, Nat.totient 111, Nat.totient 112, Nat.totient 113, Nat.totient 114, Nat.totient 115, Nat.totient 116, Nat.totient 117, Nat.totient 118, Nat.totient 119, Nat.totient 120, Nat.totient 121, Nat.totient 122, Nat.totient 123, Nat.totient 124, Nat.totient 125, Nat.totient 126, Nat.totient 127, Nat.totient 128, Nat.totient 129, Nat.totient 130, Nat.totient 131, Nat.totient 132, Nat.totient 133, Nat.totient 134, Nat.totient 135, Nat.totient 136, Nat.totient 137, Nat.totient 138, Nat.totient 139, Nat.totient 140, Nat.totient 141, Nat.totient 142, Nat.totient 143, Nat.totient 144, Nat.totient 145, Nat.totient 146, Nat.totient 147, Nat.totient 148, Nat.totient 149, Nat.totient 150, Nat.totient 151, Nat.totient 152, Nat.totient 153, Nat.totient 154, Nat.totient 155, Nat.totient 156, Nat.totient 157, Nat.totient 158, Nat.totient 159, Nat.totient 160, Nat.totient 161, Nat.totient 162, Nat.totient 163, Nat.totient 164, Nat.totient 165, Nat.totient 166, Nat.totient 167, Nat.totient 168, Nat.totient 169, Nat.totient 170, Nat.totient 171, Nat.totient 172, Nat.totient 173, Nat.totient 174, Nat.totient 175, Nat.totient 176, Nat.totient 177, Nat.totient 178, Nat.totient 179, Nat.totient 180, Nat.totient 181, Nat.totient 182, Nat.totient 183, Nat.totient 184, Nat.totient 185, Nat.totient 186, Nat.totient 187, Nat.totient 188, Nat.totient 189, Nat.totient 190, Nat.totient 191, Nat.totient 192, Nat.totient 193, Nat.totient 194, Nat.totient 195, Nat.totient 196, Nat.totient 197, Nat.totient 198, Nat.totient 199, Nat.totient 200, Nat.totient 201, Nat.totient 202, Nat.totient 203, Nat.totient 204, Nat.totient 205, Nat.totient 206, Nat.totient 207, Nat.totient 208, Nat.totient 209, Nat.totient 210, Nat.totient 211, Nat.totient 212, Nat.totient 213, Nat.totient 214, Nat.totient 215, Nat.totient 216, Nat.totient 217, Nat.totient 218, Nat.totient 219, Nat.totient 220, Nat.totient 221, Nat.totient 222, Nat.totient 223, Nat.totient 224, Nat.totient 225, Nat.totient 226, Nat.totient 227, Nat.totient 228, Nat.totient 229, Nat.totient 230, Nat.totient 231, Nat.totient 232, Nat.totient 233, Nat.totient 234, Nat.totient 235, Nat.totient 236, Nat.totient 237, Nat.totient 238, Nat.totient 239, Nat.totient 240, Nat.totient 241, Nat.totient 242, Nat.totient 243, Nat.totient 244, Nat.totient 245, Nat.totient 246, Nat.totient 247, Nat.totient 248, Nat.totient 249, Nat.totient 250, Nat.totient 251, Nat.totient 252, Nat.totient 253, Nat.totient 254, Nat.totient 255, Nat.totient 256, Nat.totient 257, Nat.totient 258, Nat.totient 259, Nat.totient 260, Nat.totient 261, Nat.totient 262, Nat.totient 263, Nat.totient 264, Nat.totient 265, Nat.totient 266, Nat.totient 267, Nat.totient 268, Nat.totient 269, Nat.totient 270, Nat.totient 271, Nat.totient 272, Nat.totient 273, Nat.totient 274, Nat.totient 275, Nat.totient 276, Nat.totient 277, Nat.totient 278, Nat.totient 279, Nat.totient 280, Nat.totient 281, Nat.totient 282, Nat.totient 283, Nat.totient 284, Nat.totient 285, Nat.totient 286, Nat.totient 287, Nat.totient 288, Nat.totient 289, Nat.totient 290, Nat.totient 291, Nat.totient 292, Nat.totient 293, Nat.totient 294, Nat.totient 295, Nat.totient 296, Nat.totient 297, Nat.totient 298, Nat.totient 299, Nat.totient 300, Nat.totient 301, Nat.totient 302, Nat.totient 303, Nat.totient 304, Nat.totient 305, Nat.totient 306, Nat.totient 307, Nat.totient 308, Nat.totient 309, Nat.totient 310, Nat.totient 311, Nat.totient 312, Nat.totient 313, Nat.totient 314, Nat.totient 315, Nat.totient 316, Nat.totient 317, Nat.totient 318, Nat.totient 319, Nat.totient 320, Nat.totient 321, Nat.totient 322, Nat.totient 323, Nat.totient 324, Nat.totient 325, Nat.totient 326, Nat.totient 327, Nat.totient 328, Nat.totient 329, Nat.totient 330, Nat.totient 331, Nat.totient 332, Nat.totient 333, Nat.totient 334, Nat.totient 335, Nat.totient 336, Nat.totient 337, Nat.totient 338, Nat.totient 339, Nat.totient 340, Nat.totient 341, Nat.totient 342, Nat.totient 343, Nat.totient 344, Nat.totient 345, Nat.totient 346, Nat.totient 347, Nat.totient 348, Nat.totient 349, Nat.totient 350, Nat.totient 351, Nat.totient 352, Nat.totient 353, Nat.totient 354, Nat.totient 355, Nat.totient 356, Nat.totient 357, Nat.totient 358, Nat.totient 359, Nat.totient 360, Nat.totient 361, Nat.totient 362, Nat.totient 363, Nat.totient 364, Nat.totient 365, Nat.totient 366, Nat.totient 367, Nat.totient 368, Nat.totient 369, Nat.totient 370, Nat.totient 371, Nat.totient 372, Nat.totient 373, Nat.totient 374, Nat.totient 375, Nat.totient 376, Nat.totient 377, Nat.totient 378, Nat.totient 379, Nat.totient 380, Nat.totient 381, Nat.totient 382, Nat.totient 383, Nat.totient 384, Nat.totient 385, Nat.totient 386, Nat.totient 387, Nat.totient 388, Nat.totient 389, Nat.totient 390, Nat.totient 391, Nat.totient 392, Nat.totient 393, Nat.totient 394, Nat.totient 395, Nat.totient 396, Nat.totient 397, Nat.totient 398, Nat.totient 399, Nat.totient 400, Nat.totient 401, Nat.totient 402, Nat.totient 403, Nat.totient 404, Nat.totient 405, Nat.totient 406, Nat.totient 407, Nat.totient 408, Nat.totient 409, Nat.totient 410, Nat.totient 411, Nat.totient 412, Nat.totient 413, Nat.totient 414, Nat.totient 415, Nat.totient 416, Nat.totient 417, Nat.totient 418, Nat.totient 419, Nat.totient 420, Nat.totient 421, Nat.totient 422, Nat.totient 423, Nat.totient 424, Nat.totient 425, Nat.totient 426, Nat.totient 427, Nat.totient 428, Nat.totient 429, Nat.totient 430, Nat.totient 431, Nat.totient 432, Nat.totient 433, Nat.totient 434, Nat.totient 435, Nat.totient 436, Nat.totient 437, Nat.totient 438, Nat.totient 439, Nat.totient 440, Nat.totient 441, Nat.totient 442, Nat.totient 443, Nat.totient 444, Nat.totient 445, Nat.totient 446, Nat.totient 447, Nat.totient 448, Nat.totient 449, Nat.totient 450, Nat.totient 451, Nat.totient 452, Nat.totient 453, Nat.totient 454, Nat.totient 455, Nat.totient 456, Nat.totient 457, Nat.totient 458, Nat.totient 459, Nat.totient 460, Nat.totient 461, Nat.totient 462, Nat.totient 463, Nat.totient 464, Nat.totient 465, Nat.totient 466, Nat.totient 467, Nat.totient 468, Nat.totient 469, Nat.totient 470, Nat.totient 471, Nat.totient 472, Nat.totient 473, Nat.totient 474, Nat.totient 475, Nat.totient 476, Nat.totient 477, Nat.totient 478, Nat.totient 479, Nat.totient 480, Nat.totient 481, Nat.totient 482, Nat.totient 483, Nat.totient 484, Nat.totient 485, Nat.totient 486, Nat.totient 487, Nat.totient 488, Nat.totient 489, Nat.totient 490, Nat.totient 491, Nat.totient 492, Nat.totient 493, Nat.totient 494, Nat.totient 495, Nat.totient 496, Nat.totient 497, Nat.totient 498, Nat.totient 499, Nat.totient 500, Nat.totient 501, Nat.totient 502, Nat.totient 503, Nat.totient 504, Nat.totient 505, Nat.totient 506, Nat.totient 507, Nat.totient 508, Nat.totient 509, Nat.totient 510, Nat.totient 511, Nat.totient 512, Nat.totient 513, Nat.totient 514, Nat.totient 515, Nat.totient 516, Nat.totient 517, Nat.totient 518, Nat.totient 519, Nat.totient 520, Nat.totient 521, Nat.totient 522, Nat.totient 523, Nat.totient 524, Nat.totient 525, Nat.totient 526, Nat.totient 527, Nat.totient 528, Nat.totient 529, Nat.totient 530, Nat.totient 531, Nat.totient 532, Nat.totient 533, Nat.totient 534, Nat.totient 535, Nat.totient 536, Nat.totient 537, Nat.totient 538, Nat.totient 539, Nat.totient 540, Nat.totient 541, Nat.totient 542, Nat.totient 543, Nat.totient 544, Nat.totient 545, Nat.totient 546, Nat.totient 547, Nat.totient 548, Nat.totient 549, Nat.totient 550, Nat.totient 551, Nat.totient 552, Nat.totient 553, Nat.totient 554, Nat.totient 555, Nat.totient 556, Nat.totient 557, Nat.totient 558, Nat.totient 559, Nat.totient 560, Nat.totient 561, Nat.totient 562, Nat.totient 563, Nat.totient 564, Nat.totient 565, Nat.totient 566, Nat.totient 567, Nat.totient 568, Nat.totient 569, Nat.totient 570, Nat.totient 571, Nat.totient 572, Nat.totient 573, Nat.totient 574, Nat.totient 575, Nat.totient 576, Nat.totient 577, Nat.totient 578, Nat.totient 579, Nat.totient 580, Nat.totient 581, Nat.totient 582, Nat.totient 583, Nat.totient 584, Nat.totient 585, Nat.totient 586, Nat.totient 587, Nat.totient 588, Nat.totient 589, Nat.totient 590, Nat.totient 591, Nat.totient 592, Nat.totient 593, Nat.totient 594, Nat.totient 595, Nat.totient 596, Nat.totient 597, Nat.totient 598, Nat.totient 599, Nat.totient 600, Nat.totient 601, Nat.totient 602, Nat.totient 603, Nat.totient 604, Nat.totient 605, Nat.totient 606, Nat.totient 607, Nat.totient 608, Nat.totient 609, Nat.totient 610, Nat.totient 611, Nat.totient 612, Nat.totient 613, Nat.totient 614, Nat.totient 615, Nat.totient 616, Nat.totient 617, Nat.totient 618, Nat.totient 619, Nat.totient 620, Nat.totient 621, Nat.totient 622, Nat.totient 623, Nat.totient 624, Nat.totient 625, Nat.totient 626, Nat.totient 627, Nat.totient 628, Nat.totient 629, Nat.totient 630, Nat.totient 631, Nat.totient 632, Nat.totient 633, Nat.totient 634, Nat.totient 635, Nat.totient 636, Nat.totient 637, Nat.totient 638, Nat.totient 639, Nat.totient 640, Nat.totient 641, Nat.totient 642, Nat.totient 643, Nat.totient 644, Nat.totient 645, Nat.totient 646, Nat.totient 647, Nat.totient 648, Nat.totient 649, Nat.totient 650, Nat.totient 651, Nat.totient 652, Nat.totient 653, Nat.totient 654, Nat.totient 655, Nat.totient 656, Nat.totient 657, Nat.totient 658, Nat.totient 659, Nat.totient 660, Nat.totient 661, Nat.totient 662, Nat.totient 663, Nat.totient 664, Nat.totient 665, Nat.totient 666, Nat.totient 667, Nat.totient 668, Nat.totient 669, Nat.totient 670, Nat.totient 671, Nat.totient 672, Nat.totient 673, Nat.totient 674, Nat.totient 675, Nat.totient 676, Nat.totient 677, Nat.totient 678, Nat.totient 679, Nat.totient 680, Nat.totient 681, Nat.totient 682, Nat.totient 683, Nat.totient 684, Nat.totient 685, Nat.totient 686, Nat.totient 687, Nat.totient 688, Nat.totient 689, Nat.totient 690, Nat.totient 691, Nat.totient 692, Nat.totient 693, Nat.totient 694, Nat.totient 695, Nat.totient 696, Nat.totient 697, Nat.totient 698, Nat.totient 699, Nat.totient 700, Nat.totient 701, Nat.totient 702, Nat.totient 703, Nat.totient 704, Nat.totient 705, Nat.totient 706, Nat.totient 707, Nat.totient 708, Nat.totient 709, Nat.totient 710, Nat.totient 711, Nat.totient 712, Nat.totient 713, Nat.totient 714, Nat.totient 715, Nat.totient 716, Nat.totient 717, Nat.totient 718, Nat.totient 719, Nat.totient 720, Nat.totient 721, Nat.totient 722, Nat.totient 723, Nat.totient 724, Nat.totient 725, Nat.totient 726, Nat.totient 727, Nat.totient 728, Nat.totient 729, Nat.totient 730, Nat.totient 731, Nat.totient 732, Nat.totient 733, Nat.totient 734, Nat.totient 735, Nat.totient 736, Nat.totient 737, Nat.totient 738, Nat.totient 739, Nat.totient 740, Nat.totient 741, Nat.totient 742, Nat.totient 743, Nat.totient 744, Nat.totient 745, Nat.totient 746, Nat.totient 747, Nat.totient 748, Nat.totient 749, Nat.totient 750, Nat.totient 751, Nat.totient 752, Nat.totient 753, Nat.totient 754, Nat.totient 755, Nat.totient 756, Nat.totient 757, Nat.totient 758, Nat.totient 759, Nat.totient 760, Nat.totient 761, Nat.totient 762, Nat.totient 763, Nat.totient 764, Nat.totient 765, Nat.totient 766, Nat.totient 767, Nat.totient 768, Nat.totient 769, Nat.totient 770, Nat.totient 771, Nat.totient 772, Nat.totient 773, Nat.totient 774, Nat.totient 775, Nat.totient 776, Nat.totient 777, Nat.totient 778, Nat.totient 779, Nat.totient 780, Nat.totient 781, Nat.totient 782, Nat.totient 783, Nat.totient 784, Nat.totient 785, Nat.totient 786, Nat.totient 787, Nat.totient 788, Nat.totient 789, Nat.totient 790, Nat.totient 791, Nat.totient 792, Nat.totient 793, Nat.totient 794, Nat.totient 795, Nat.totient 796, Nat.totient 797, Nat.totient 798, Nat.totient 799, Nat.totient 800, Nat.totient 801, Nat.totient 802, Nat.totient 803, Nat.totient 804, Nat.totient 805, Nat.totient 806, Nat.totient 807, Nat.totient 808, Nat.totient 809, Nat.totient 810, Nat.totient 811, Nat.totient 812, Nat.totient 813, Nat.totient 814, Nat.totient 815, Nat.totient 816, Nat.totient 817, Nat.totient 818, Nat.totient 819, Nat.totient 820, Nat.totient 821, Nat.totient 822, Nat.totient 823, Nat.totient 824, Nat.totient 825, Nat.totient 826] = values
  simp only [phi_0, phi_1, phi_2, phi_3, phi_4, phi_5, phi_6, phi_7, phi_8, phi_9, phi_10, phi_11, phi_12, phi_13, phi_14, phi_15, phi_16, phi_17, phi_18, phi_19, phi_20, phi_21, phi_22, phi_23, phi_24, phi_25, phi_26, phi_27, phi_28, phi_29, phi_30, phi_31, phi_32, phi_33, phi_34, phi_35, phi_36, phi_37, phi_38, phi_39, phi_40, phi_41, phi_42, phi_43, phi_44, phi_45, phi_46, phi_47, phi_48, phi_49, phi_50, phi_51, phi_52, phi_53, phi_54, phi_55, phi_56, phi_57, phi_58, phi_59, phi_60, phi_61, phi_62, phi_63, phi_64, phi_65, phi_66, phi_67, phi_68, phi_69, phi_70, phi_71, phi_72, phi_73, phi_74, phi_75, phi_76, phi_77, phi_78, phi_79, phi_80, phi_81, phi_82, phi_83, phi_84, phi_85, phi_86, phi_87, phi_88, phi_89, phi_90, phi_91, phi_92, phi_93, phi_94, phi_95, phi_96, phi_97, phi_98, phi_99, phi_100, phi_101, phi_102, phi_103, phi_104, phi_105, phi_106, phi_107, phi_108, phi_109, phi_110, phi_111, phi_112, phi_113, phi_114, phi_115, phi_116, phi_117, phi_118, phi_119, phi_120, phi_121, phi_122, phi_123, phi_124, phi_125, phi_126, phi_127, phi_128, phi_129, phi_130, phi_131, phi_132, phi_133, phi_134, phi_135, phi_136, phi_137, phi_138, phi_139, phi_140, phi_141, phi_142, phi_143, phi_144, phi_145, phi_146, phi_147, phi_148, phi_149, phi_150, phi_151, phi_152, phi_153, phi_154, phi_155, phi_156, phi_157, phi_158, phi_159, phi_160, phi_161, phi_162, phi_163, phi_164, phi_165, phi_166, phi_167, phi_168, phi_169, phi_170, phi_171, phi_172, phi_173, phi_174, phi_175, phi_176, phi_177, phi_178, phi_179, phi_180, phi_181, phi_182, phi_183, phi_184, phi_185, phi_186, phi_187, phi_188, phi_189, phi_190, phi_191, phi_192, phi_193, phi_194, phi_195, phi_196, phi_197, phi_198, phi_199, phi_200, phi_201, phi_202, phi_203, phi_204, phi_205, phi_206, phi_207, phi_208, phi_209, phi_210, phi_211, phi_212, phi_213, phi_214, phi_215, phi_216, phi_217, phi_218, phi_219, phi_220, phi_221, phi_222, phi_223, phi_224, phi_225, phi_226, phi_227, phi_228, phi_229, phi_230, phi_231, phi_232, phi_233, phi_234, phi_235, phi_236, phi_237, phi_238, phi_239, phi_240, phi_241, phi_242, phi_243, phi_244, phi_245, phi_246, phi_247, phi_248, phi_249, phi_250, phi_251, phi_252, phi_253, phi_254, phi_255, phi_256, phi_257, phi_258, phi_259, phi_260, phi_261, phi_262, phi_263, phi_264, phi_265, phi_266, phi_267, phi_268, phi_269, phi_270, phi_271, phi_272, phi_273, phi_274, phi_275, phi_276, phi_277, phi_278, phi_279, phi_280, phi_281, phi_282, phi_283, phi_284, phi_285, phi_286, phi_287, phi_288, phi_289, phi_290, phi_291, phi_292, phi_293, phi_294, phi_295, phi_296, phi_297, phi_298, phi_299, phi_300, phi_301, phi_302, phi_303, phi_304, phi_305, phi_306, phi_307, phi_308, phi_309, phi_310, phi_311, phi_312, phi_313, phi_314, phi_315, phi_316, phi_317, phi_318, phi_319, phi_320, phi_321, phi_322, phi_323, phi_324, phi_325, phi_326, phi_327, phi_328, phi_329, phi_330, phi_331, phi_332, phi_333, phi_334, phi_335, phi_336, phi_337, phi_338, phi_339, phi_340, phi_341, phi_342, phi_343, phi_344, phi_345, phi_346, phi_347, phi_348, phi_349, phi_350, phi_351, phi_352, phi_353, phi_354, phi_355, phi_356, phi_357, phi_358, phi_359, phi_360, phi_361, phi_362, phi_363, phi_364, phi_365, phi_366, phi_367, phi_368, phi_369, phi_370, phi_371, phi_372, phi_373, phi_374, phi_375, phi_376, phi_377, phi_378, phi_379, phi_380, phi_381, phi_382, phi_383, phi_384, phi_385, phi_386, phi_387, phi_388, phi_389, phi_390, phi_391, phi_392, phi_393, phi_394, phi_395, phi_396, phi_397, phi_398, phi_399, phi_400, phi_401, phi_402, phi_403, phi_404, phi_405, phi_406, phi_407, phi_408, phi_409, phi_410, phi_411, phi_412, phi_413, phi_414, phi_415, phi_416, phi_417, phi_418, phi_419, phi_420, phi_421, phi_422, phi_423, phi_424, phi_425, phi_426, phi_427, phi_428, phi_429, phi_430, phi_431, phi_432, phi_433, phi_434, phi_435, phi_436, phi_437, phi_438, phi_439, phi_440, phi_441, phi_442, phi_443, phi_444, phi_445, phi_446, phi_447, phi_448, phi_449, phi_450, phi_451, phi_452, phi_453, phi_454, phi_455, phi_456, phi_457, phi_458, phi_459, phi_460, phi_461, phi_462, phi_463, phi_464, phi_465, phi_466, phi_467, phi_468, phi_469, phi_470, phi_471, phi_472, phi_473, phi_474, phi_475, phi_476, phi_477, phi_478, phi_479, phi_480, phi_481, phi_482, phi_483, phi_484, phi_485, phi_486, phi_487, phi_488, phi_489, phi_490, phi_491, phi_492, phi_493, phi_494, phi_495, phi_496, phi_497, phi_498, phi_499, phi_500, phi_501, phi_502, phi_503, phi_504, phi_505, phi_506, phi_507, phi_508, phi_509, phi_510, phi_511, phi_512, phi_513, phi_514, phi_515, phi_516, phi_517, phi_518, phi_519, phi_520, phi_521, phi_522, phi_523, phi_524, phi_525, phi_526, phi_527, phi_528, phi_529, phi_530, phi_531, phi_532, phi_533, phi_534, phi_535, phi_536, phi_537, phi_538, phi_539, phi_540, phi_541, phi_542, phi_543, phi_544, phi_545, phi_546, phi_547, phi_548, phi_549, phi_550, phi_551, phi_552, phi_553, phi_554, phi_555, phi_556, phi_557, phi_558, phi_559, phi_560, phi_561, phi_562, phi_563, phi_564, phi_565, phi_566, phi_567, phi_568, phi_569, phi_570, phi_571, phi_572, phi_573, phi_574, phi_575, phi_576, phi_577, phi_578, phi_579, phi_580, phi_581, phi_582, phi_583, phi_584, phi_585, phi_586, phi_587, phi_588, phi_589, phi_590, phi_591, phi_592, phi_593, phi_594, phi_595, phi_596, phi_597, phi_598, phi_599, phi_600, phi_601, phi_602, phi_603, phi_604, phi_605, phi_606, phi_607, phi_608, phi_609, phi_610, phi_611, phi_612, phi_613, phi_614, phi_615, phi_616, phi_617, phi_618, phi_619, phi_620, phi_621, phi_622, phi_623, phi_624, phi_625, phi_626, phi_627, phi_628, phi_629, phi_630, phi_631, phi_632, phi_633, phi_634, phi_635, phi_636, phi_637, phi_638, phi_639, phi_640, phi_641, phi_642, phi_643, phi_644, phi_645, phi_646, phi_647, phi_648, phi_649, phi_650, phi_651, phi_652, phi_653, phi_654, phi_655, phi_656, phi_657, phi_658, phi_659, phi_660, phi_661, phi_662, phi_663, phi_664, phi_665, phi_666, phi_667, phi_668, phi_669, phi_670, phi_671, phi_672, phi_673, phi_674, phi_675, phi_676, phi_677, phi_678, phi_679, phi_680, phi_681, phi_682, phi_683, phi_684, phi_685, phi_686, phi_687, phi_688, phi_689, phi_690, phi_691, phi_692, phi_693, phi_694, phi_695, phi_696, phi_697, phi_698, phi_699, phi_700, phi_701, phi_702, phi_703, phi_704, phi_705, phi_706, phi_707, phi_708, phi_709, phi_710, phi_711, phi_712, phi_713, phi_714, phi_715, phi_716, phi_717, phi_718, phi_719, phi_720, phi_721, phi_722, phi_723, phi_724, phi_725, phi_726, phi_727, phi_728, phi_729, phi_730, phi_731, phi_732, phi_733, phi_734, phi_735, phi_736, phi_737, phi_738, phi_739, phi_740, phi_741, phi_742, phi_743, phi_744, phi_745, phi_746, phi_747, phi_748, phi_749, phi_750, phi_751, phi_752, phi_753, phi_754, phi_755, phi_756, phi_757, phi_758, phi_759, phi_760, phi_761, phi_762, phi_763, phi_764, phi_765, phi_766, phi_767, phi_768, phi_769, phi_770, phi_771, phi_772, phi_773, phi_774, phi_775, phi_776, phi_777, phi_778, phi_779, phi_780, phi_781, phi_782, phi_783, phi_784, phi_785, phi_786, phi_787, phi_788, phi_789, phi_790, phi_791, phi_792, phi_793, phi_794, phi_795, phi_796, phi_797, phi_798, phi_799, phi_800, phi_801, phi_802, phi_803, phi_804, phi_805, phi_806, phi_807, phi_808, phi_809, phi_810, phi_811, phi_812, phi_813, phi_814, phi_815, phi_816, phi_817, phi_818, phi_819, phi_820, phi_821, phi_822, phi_823, phi_824, phi_825, phi_826]
  rfl

theorem values_correct (n : Nat) (hn : n < 827) : Nat.totient n = values[n]?.getD 0 := by
  have h := congrArg (fun l : List Nat => l[n]?.getD 0) values_eq
  simpa [hn] using h

end Erdos415.Certificate
