-- Run: `lake env lean checks/ces_axioms.lean`.
-- Every line must list only [propext, Classical.choice, Quot.sound]; `sorryAx` means a gap.
import CES
#print axioms CES.P_pos
#print axioms CES.share_eq
#print axioms CES.share_sum
#print axioms CES.expenditure
#print axioms CES.budget
#print axioms CES.indirect_utility
