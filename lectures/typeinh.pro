% термове
% 1. x, y, z
% 2. app(M, N)
% 3. λ(X, M)

% !!! λ(app(x, y), z)
% !!! λ(john, mary)

% типове
% 1. α, β, γ
% 2. arr(Ρ, Σ)

% !!! arr(λ(x, x), τ)

% типово съждение
% isa(M, Τ).
% M : Τ

% типов контекст
% списък от типови декларации
% Пример: [ isa(x, α), isa(y, arr(α, β)) ]

% types(Γ, isa(M, Τ))
% Γ ⊢ M : Τ

:- set_prolog_flag(occurs_check, true).

isI(λ(x, x)).
isK(λ(x, λ(y, x))).
isKs(λ(x, λ(y, y))).
isS(λ(x, λ(y, λ(z, app(app(x, z), app(y, z)))))).
isω(λ(x, app(x, x))).
isY(λ(f, app( λ(x, app(f, app(x, x))), λ(x, app(f, app(x, x)))))).
isΩ(app(M, M)) :- isω(M).
isC1(λ(x, λ(f, app(f, x)))).
isC2(λ(x, λ(f, app(f, app(f, x))))).

isIType(arr(α, α)).
isKType(arr(α, arr(β, α))).
isKsType(arr(β, arr(α, α))).
isSType(arr(arr(α, arr(β, γ)), arr(arr(α, β), arr(α, γ)))).
isCType(arr(α, arr(arr(α, α), α))).
isBadType1(arr(arr(α, β), β)).
isBadType2(arr(arr(α, β), arr(arr(β, α), β))).
isGoodType(arr(arr(α, β), arr(arr(arr(β, β), α), β))).

% listargtypes(-ΡL, -Α, +Τ)
listargtypes([], Τ, Τ).
listargtypes([Ρ | ΡL], Α, arr(Ρ, Σ))  :- listargtypes(ΡL, Α, Σ).

% typesall(+Γ, -NL, +ΡL)
typesall(_      , _, [], []).
typesall(Visited, Γ, [N | NL],  [Ρ | ΡL]) :- types(Visited, Γ, isa(N, Ρ)),
                                             typesall(Visited, Γ, NL, ΡL).

% applyall(+X, +NL, -M)
applyall(X, [], X).
applyall(X, [N | NL], M) :- applyall(app(X, N), NL, M).

% искаме да се използва така:
% types(+Γ, isa(-M, +Τ))
types(_      , Γ, isa(λ(X, N), arr(Ρ, Σ)))   :- types([], [ isa(X, Ρ) | Γ ], isa(N, Σ)).
types(Visited, Γ, isa(M, Α))                 :- not(member(Α, Visited)),
                                                member(isa(X, Τ), Γ),
                                                % Τ ≡ ρ₁ ⇒ ρ₂ ⇒ ... ⇒ ρₖ ⇒ α
                                                % Τ = arr(Ρ1, arr(Ρ2, ..., arr(Ρk, Α)...))
                                                listargtypes(ΡL, Α, Τ),
                                                % Γ ⊢ N₁ : ρ₁, ... Γ ⊢ Nₖ : ρₖ
                                                % types(Γ, isa(N1, Ρ1)),
                                                % ...
                                                % types(Γ, isa(Nk, Ρk)),
                                                typesall([Α | Visited], Γ, NL, ΡL),
                                                % M ≡ xN₁N₂...Nₖ
                                                % M = app(app(...app(X, N1), N2), ..., Nk)
                                                applyall(X, NL, M).

types(TypeStatement)                :- types([], [], TypeStatement).
