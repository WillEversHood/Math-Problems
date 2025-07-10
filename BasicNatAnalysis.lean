section

theorem T
  (a b c d e : Nat)
  (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : 1 + d = e) :
  a = e :=
  calc
    a = b := h1
    b = c + 1:= h2
    c + 1 = d + 1 := congrArg Nat.succ h3
    d + 1 = 1 + d := Nat.add_comm d 1
    1 + d = e := h4

#check T

end
