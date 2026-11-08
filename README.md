# Projeto de Formalização em Isabelle da Disciplina de Formalismos Matemáticos da Computação

Formalização em Isabelle/HOL de resultados do livro *Term Rewriting and All That*, de Franz Baader e Tobias Nipkow, com ênfase na confluência de sistemas ortogonais e paralelamente fechados (Capítulo 6). As provas seguem as do livro: a redução paralela é definida, como na Definição 6.3.7, pela contração simultânea de redexes num conjunto de posições paralelas.

## Principais resultados

| Livro | Resultado | Nome na formalização |
|---|---|---|
| Fato 6.3.8 | `→ ⊆ ⇉ ⊆ →*` | `rstep_subset_par_rstep`, `par_rstep_subset_rtrancl` |
| Lema 6.4.1 | `⇉` é fechada por contextos | `par_rstep_ctxt` |
| Lema 6.4.2 | `σ(x) ⇉ τ(x)` para `x ∈ Var(t)` implica `σ(t) ⇉ τ(t)` | `par_rstep_subst` |
| Lema 6.4.4 | Lema dos movimentos paralelos | `par_rstep_at_linear` |
| Teorema 6.3.10 | Em um SRT ortogonal, `⇉` tem a propriedade do diamante | `orthogonal_par_rstep_diamond` |
| Corolário 6.3.11 | Todo SRT ortogonal é confluente | `orthogonal_imp_confluent` |
| Teorema 6.4.8 | Teorema do fecho paralelo (Huet) | `parallel_closure_theorem` |
| Corolário 6.4.9 | Todo SRT linear à esquerda e paralelamente fechado é confluente | `left_linear_parallel_closed_imp_confluent` |

Também estão formalizados o Lema dos Pares Críticos (6.2.3), o Teorema dos Pares Críticos (6.2.4), o Lema da Confluência Forte (6.3.3) e a existência de unificadores mais gerais (Teorema 4.5.8).

## Estrutura

As teorias ficam em `thys/` (sessão `Formalismos`, sobre `HOL`):

| Teoria | Conteúdo |
|---|---|
| `Relations` | Relações binárias e composição |
| `Reduction_Systems` | Sistemas de redução abstratos (Capítulo 2) |
| `Partial_Orders` | Ordens |
| `Multisets`, `Multisets_WF` | Naturais estendidos, multiconjuntos e boa fundação da extensão multiconjunto |
| `Commutation` | Propriedade do diamante |
| `Terms` | Termos, posições, substituições (Seção 3.1) |
| `Term_Rewriting` | Relação de reescrita e sistemas de reescrita de termos |
| `Unification` | Unificadores mais gerais (Seção 4.5) |
| `Confluence` | Pares críticos, linearidade, redução paralela e sistemas ortogonais (Seções 6.1–6.3) |
| `Parallel_Closed` | Sistemas paralelamente fechados (Seção 6.4) |

O documento `document/Formalismos Matemáticos.tex` apresenta as provas em português, indicando ao lado de cada enunciado o número no livro e o nome do fato na formalização, com link para o GitHub.

## Como verificar

Com o Isabelle2025-2 instalado, abra as teorias no Isabelle/jEdit:

```sh
isabelle jedit -d thys thys/Parallel_Closed.thy
```

Para verificar a sessão inteira em lote:

```sh
isabelle build -D thys
```

O arquivo `thys/ROOT` declara `document_files "root.tex"`, mas `thys/document/root.tex` ainda não existe. Enquanto ele não for criado, o `isabelle build` falha antes de verificar as teorias; para contornar, remova a linha `document_files` (e o `root.tex` abaixo dela) do `ROOT`.

## Como gerar o documento

```sh
cd document
python3 isa_links.py        # atualiza isa-links.tex com os links para as teorias
latexmk -pdf "Formalismos Matemáticos.tex"
```

Rode `isa_links.py` sempre que as teorias mudarem, para que os links apontem para as linhas corretas.
