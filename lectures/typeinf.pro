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

% използваме така
% types(+Γ, isa(+M, ?Τ))

% може ли да се използва така:
% types(+Γ, isa(-M, +Τ))

types(Γ, Decl)                      :- member(Decl, Γ).
types(Γ, isa(app(M1, M2), Σ))       :- types(Γ, isa(M1, arr(Ρ, Σ))),
                                       types(Γ, isa(M2, Ρ)).
types(Γ, isa(λ(X, N), arr(Ρ, Σ)))   :- not(member(isa(X, _), Γ)),
                                       types([ isa(X, Ρ) | Γ ], isa(N, Σ)).

types(isa(M, Τ))                    :- types([], isa(M, Τ)).
typeable(M)                         :- types(isa(M, _)).
