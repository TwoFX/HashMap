

theorem evil : Nat = Bool := sorry

def magicBool : Bool := cast evil 4
def magicNat : Nat := cast evil.symm False

#eval magicNat
-- #eval magicBool
