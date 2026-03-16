import Init

namespace List
  /- Set-Like Conversion -/
  prefix:max "#" => List.eraseDups
  /- Set-Like Union: l₁ ∪ l₂ = {a | a ∈ l₁ ∨ a ∈ l₂} -/
  notation:66 l₁:40 " ∪ " l₂:40 => List.eraseDups (List.append l₁ l₂)
  /- Set-Like Subtraction: l₁ − l₂ = {a | a ∈ l₁ ∧ a ∉ l₂} -/
  notation:66 l₁:40 " − " l₂:40 => List.eraseDups (List.removeAll l₁ l₂)
end List

/- End -/
