import random

def voc_block(n, preds, functions):
    block = 'vocabulary {\n'
    typeA = '\ttype A := { a' + ', a'.join(map(str,list(range(n)))) + ' }'
    typeB = '\ttype B := { b' + ', b'.join(map(str,list(range(n)))) + ' }'
    block += typeA + '\n' + typeB + '\n'
    for p in preds :
        block += f'\t{p}: A * B -> Bool\n'
    for f in functions:
        block += f'\t{f[0]}: {' * '.join(f[1])} -> {f[2]}\n'
    return block + '}'

def theory_block(formulas):
    block = 'theory {\n'
    for f in formulas:
        block += f'\t{f}\n'
    return block + '}'

def fill_structure_for_predicate(pred, n, a_every, b_every, positive):
    line = f'{pred} := ' + '{ '
    for i in range(n):
        for j in range(n):
            if positive and i%a_every == 0 and j%b_every == 0:
                line += f'(a{i},b{j}), '
            elif not positive and (i%a_every != 0 or j%b_every != 0):
                line += f'(a{i},b{j}), '
    return line[:-2] + ' }.'

def structure_block(fills):
    block = 'structure {\n'
    for f in fills:
        block += '\t' + f + '\n'
    return block + '}'

def get_formulas(a_case, b_case, n):
    formulas = []
    if a_case == "A1":
        formulas = ['!x in A: !y in B: (P(x,y) | q(x,y)).']
        if b_case == 'Bt':
            formulas.append('!x in A: !y in B: (S(x,y) => q(x,y)).')
    if a_case == 'A2':
        formulas = ['!x in A: !y in B: (P(x,y) | Q(x,y) | (f(x,y) = b0)).']
        if b_case == 'Bt':
            formulas.append('!x in A: !y in B: (~S(x,y) => (f(x,y) ~= b0)).')
    if a_case == 'A3':
        formulas = ['?x in A: ?y in B: (P(x,y) & q(x,y)).']
        if b_case == 'Bt':
            formulas.append('!x in A: !y in B: (~S(x,y) => ~q(x,y)).')
    if a_case == 'A4':
        formulas = ['?x in A: ?y in B: (P(x,y) & (Q(x,y) | (f(x)=y))).']
        if b_case == 'Bt':
            rand_a = random.randrange(0,n)
            rand_b = random.randrange(0,n)
            formulas.append(f'f(a{rand_a})=b{rand_b}.')
    if a_case == 'A5':
        formulas = ['!x in A: ?y in B: (P(x,y) | q(x,y)).']
    if a_case == 'A6':
        formulas = ['!x in A: ?y in B: (P(x,y) & (r(x,y) | Q(x,y))).']
        if b_case == 'Bs':
            formulas.append('!x in A: !y in B: (P(x,y) => r(x,y)).')
    if a_case == 'A7':
        formulas = ['?x in A: !y in B: ((P(x,y) & q(x,y)).']
        if b_case == 'Bs':
            formulas.append('!x in A: !y in B: (P(x,y) => q(x,y)).')
    if a_case == 'A8':
        formulas = ['?x in A: !y in B: (P(x,y) | (r(x,y) & Q(x,y))).']
    return formulas

def generate_case(a_case, b_case, n):
    theory = theory_block(get_formulas(a_case, b_case, n))
    if a_case == 'A1':
        if b_case == 'Bs' or b_case == 'Bf':
            vocabulary = voc_block(n, ['P', 'q'], [])
            if b_case == 'Bs':
                fillP = fill_structure_for_predicate('P', n, 4, 5, True)
            else:
                fillP = fill_structure_for_predicate('P', n, 100, 10, False)
            structure = structure_block([fillP])
        if b_case == 'Bt':
            vocabulary = voc_block(n, ['S','P', 'q'], [])
            fillP = fill_structure_for_predicate('P', n, 4, 5, True)
            fillS = fill_structure_for_predicate('S', n, 4, 5, False)
            structure = structure_block([fillP,fillS])
    elif a_case == 'A2':
        if b_case == 'Bs' or b_case == 'Bf':
            vocabulary = voc_block(n, ['P', 'Q'], [['f', ['A','B'], 'B']])
            if b_case == 'Bs':
                fillP = fill_structure_for_predicate('P', n, 4, 5, True)
                fillQ = fill_structure_for_predicate('Q', n, 4, 5, True)
            else:
                fillP = fill_structure_for_predicate('P', n, 20, 25, False)
                as_list = fillP.split(', ')
                split_at_index = fillP.count(', ') // 2
                fillP = ', '.join(as_list[:split_at_index]) + ' }.'
                fillQ = 'Q := { ' + ', '.join(as_list[split_at_index:])
            structure = structure_block([fillP,fillQ])
        if b_case == 'Bt':
            vocabulary = voc_block(n, ['P', 'Q', 'S'], [['f', ['A','B'], 'B']])
            fillP = fill_structure_for_predicate('P', n, 4, 5, True)
            fillQ = fill_structure_for_predicate('Q', n, 4, 5, True)
            fillS = 'S := { }.'
            structure = structure_block([fillP,fillQ,fillS])
    elif a_case == 'A3':
        if b_case == 'Bs' or b_case == 'Bf':
            vocabulary = voc_block(n, ['P', 'q'], [])
            if b_case == 'Bs':
                fillP = fill_structure_for_predicate('P', n, 10, 10, True)
            else:
                fillP = fill_structure_for_predicate('P', n, 1, 1, True)
            structure = structure_block([fillP])
        if b_case == 'Bt':
            vocabulary = voc_block(n, ['P', 'q', 'S'], [])
            fillP = fill_structure_for_predicate('P', n, 10, 10, True)
            fillS = 'S := { }.'
            structure = structure_block([fillP,fillS])
    elif a_case == 'A4':
        vocabulary = voc_block(n, ['P','Q'], [['f',['A'],'B']])
        if b_case == 'Bt':
            fillP = fill_structure_for_predicate('P', n, 1, 1, True)
            fillQ = 'Q := {  }.'
        if b_case == 'Bs':
            fillP = fill_structure_for_predicate('P', n, 10, 10, True)
            fillQ = fill_structure_for_predicate('Q', n, 2, 1, False)
        if b_case == 'Bf':
            fillP = fill_structure_for_predicate('P', n, 4, 5, False)
            fillQ = 'Q := {  }.'
        structure = structure_block([fillP,fillQ])
    elif a_case == 'A5':
        vocabulary = voc_block(n, ['P','q'], [])
        fillP = 'P := { '
        if b_case == 'Bt':
            for i in range(n):
                fillP += f'(a{i},b{i}), '
        if b_case == 'Bs':
            for i in range(0,n,20):
                for j in range(n):
                    fillP += f'(a{i},b{j}), '
        if b_case == 'Bf':
            for i in range(n):
                if i % 20 != 0:
                    for j in range(n):
                        fillP += f'(a{i},b{j}), '
        fillP = fillP[:-2] + ' }. '
        structure = structure_block([fillP])
    elif a_case == 'A6':
        vocabulary = voc_block(n, ['P','r', 'Q'], [])
        fillP = 'P := { '
        fillQ = 'Q := { '
        if b_case == 'Bt' or b_case == 'Bf':
            for i in range(n):
                rand_b = random.randrange(0,n-1)
                if rand_b % 2 == 1:
                    rand_b += 1
                if b_case == 'Bf':
                    rand_b = 1
                for j in range(n):
                    if j % 2 == 0:
                        fillP += f'(a{i},b{j}), '
                    if j % 2 != 0 or j == rand_b:
                        fillQ += f'(a{i},b{j}), '
        if b_case == 'Bs':
            for i in range(n-1):
                fillP += f'(a{i},b{i}), '
                fillQ += f'(a{i},b{i+1}), '
            fillP += f'(a{n-1},b{n-1}), '
        fillP = fillP[:-2] + ' }. '
        fillQ = fillQ[:-2] + ' }. '
        structure = structure_block([fillP,fillQ])
    elif a_case == 'A7':
        vocabulary = voc_block(n, ['P','q'], [])
        if b_case == 'Bt':
            fillP = 'P := { '
            for i in range(n):
                exclude_j = random.randrange(0,n)
                for j in range(n):
                    if j != exclude_j:
                        fillP += f'(a{i},b{j}), '
            fillP = fillP[:-2] + ' }. '
        if b_case == 'Bs':
            fillP = 'P := { '
            random_k = random.randrange(0,n)
            for i in range(n):
                if i == random_k:
                    for j in range(n):
                        fillP += f'(a{i},b{j}), '
                else:
                    fillP += f'(a{i},b{i}), '
            fillP = fillP[:-2] + ' }. '
        if b_case == 'Bf':
            fillP = fill_structure_for_predicate('P', n, 1, 1, True)
        structure = structure_block([fillP])
    else:
        vocabulary = voc_block(n, ['P', 'Q', 'r'], [])
        if b_case == 'Bt':
            fillQ = 'Q := { }. '
            fillP = 'P := { '
            random_k = random.randrange(0,n)
            for j in range(n):
                fillP += f'(a{random_k},b{j}), '
            fillP = fillP[:-2] + ' }. '
        if b_case == 'Bs':
            fillQ = 'Q := { '
            fillP = 'P := { '
            for i in range(0,n,100):
                for j in range(n):
                    if j%2 == 0:
                        fillP += f'(a{i},b{j}), '
                    else:
                        fillQ += f'(a{i},b{j}), '
            fillP = fillP[:-2] + ' }. '
            fillQ = fillQ[:-2] + ' }. '
        if b_case == 'Bf':
            fillP = fill_structure_for_predicate('P', n, 1, 2, True)
            fillQ = fillQ = 'Q := { '
            for i in range(n):
                for j in range(1,n,2):
                    fillQ += f'(a{i},b{j}), '
            fillQ = fillQ[:-2] + ' }. '
        structure = structure_block([fillQ, fillP])
    return vocabulary + '\n\n' + structure + '\n\n' + theory

make_case_manually = False
#make_case_manually = True
if make_case_manually:
    with open("test_case_manual.idp", "w") as file:
        file.write(generate_case('A8', 'Bf', 6))







