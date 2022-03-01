import math,random
def generateprimes(upperbound):
    booleanlist = [True] * (upperbound - 1)
    upperboundofupperbound = int(math.sqrt(upperbound))
    for index in range(upperboundofupperbound - 1):
        if booleanlist[index] == True:
            jindex = 2 * index + 2
            while jindex < upperbound - 1:
                booleanlist[jindex] = False
                jindex += index + 2
    primes = []
    for index in range(upperbound - 1):
        if booleanlist[index] == True:
            primes += [index + 2]
    return primes
def eea(rzero,rone):
    szero = 1
    sone = 0
    while rone:
        quotient = rzero // rone
        rzero,rone = rone,rzero - quotient * rone
        szero,sone = sone,szero - quotient * sone
    return rzero,szero
def millerrabin(n,base):
    nminusone = n - 1
    r = 0
    d = nminusone
    while not d & 1:
        r += 1
        d >>= 1
    x = pow(base,d,n)
    if x in [1,nminusone]:
        return True
    for _ in range(r - 1):
        x = (x * x) % n
        if x == nminusone:
            return True
    return False
def isprime(n):
    if n < 2:
        return False
    if n < 4:
        return True
    nminustwo = n - 2
    for _ in range(23):
        base = random.randint(2,nminustwo)
        if math.gcd(n,base) > 1 or not millerrabin(n,base):
            return False
    return True
dejavu = {}
factofile = open("factorizations.txt","r")
lines = factofile.readlines()
factofile.close()
for line in lines:
    composite,factorization,leftover = line[:-1].split(" ")
    facto = {}
    for primepower in factorization.split("."):
        prime,power = map(int,primepower.split("^"))
        facto[prime] = power
    dejavu[int(composite)] = (facto,int(leftover))
factofile = open("factorizations.txt","a")
def pollardsrho(n,limit,hardness):
    if n in dejavu:
        facto,leftover = dejavu[n]
        return facto.copy(),leftover
    if isprime(n):
        dejavu[n] = ({n:1},1)
        return {n:1},1
    seed = random.randint(1,n - 1)
    factor = n
    numgcds = 0
    while factor == n:
        x = seed
        cycle = 2
        unfactored = True
        while unfactored:
            y = x
            for _ in range(cycle):
                x = (x * x + 1) % n
                factor = math.gcd(x - y,n)
                if factor > 1:
                    unfactored = False
                    break
                numgcds += 1
                if numgcds == limit:
                    return {},n
            cycle <<= 1
        seed += 1
    firstfacto,firstleftover = pollardsrho(factor,limit,hardness)
    secondfacto,secondleftover = pollardsrho(n // factor,limit,hardness)
    for prime in secondfacto:
        if prime in firstfacto:
            firstfacto[prime] += secondfacto[prime]
        else:
            firstfacto[prime] = secondfacto[prime]
    leftover = firstleftover * secondleftover
    dejavu[n] = (firstfacto.copy(),leftover)
    if (leftover == 1 and len(firstfacto) > 1 and sorted(firstfacto)[-2] > hardness) or (leftover > 1 and firstfacto and sorted(firstfacto)[-1] > hardness):
        facto = []
        for prime in firstfacto:
            facto += [str(prime) + "^" + str(firstfacto[prime])]
        factofile.write(" ".join((str(n),".".join(facto),str(leftover))) + "\n")
        factofile.flush()
    return firstfacto,leftover
def isprimeforsure(n,factolimit,hardness,witlimit,triallimit):
    if n < 3317044064679887385961981:
        for base in [2,3,5,7,11,13,17,19,23,29,31,37,41]:
            if n == base:
                return True
            if not millerrabin(n,base):
                return False
        return True
    nminusone = n - 1
    nminustwo = n - 2
    R = nminusone
    Ffacto = {}
    while True:
        facto,R = pollardsrho(R,factolimit,hardness)
        for prime in facto:
            if prime in Ffacto:
                Ffacto[prime] += facto[prime]
            else:
                Ffacto[prime] = facto[prime]
        pseudoprimes = set(Ffacto)
        F = nminusone // R
        s,r = divmod(R,F << 1)
        if n < (R * F + 1) * (((F * F) << 1) + (r - R) * F + 1):
            primes = list(Ffacto)
            if R > 1:
                primes += [R]
            for p in primes:
                witnessfound = False
                for _ in range(witlimit):
                    a = random.randint(2,nminustwo)
                    if math.gcd(a,n) > 1:
                        return False
                    if pow(a,nminusone,n) == 1 == math.gcd(pow(a,nminusone // p,n) - 1,n):
                        witnessfound = True
                        break
                if not witnessfound:
                    return False
            result = True
            inequalityachieved = True
            if R > 1:
                inequalityacheived = isprime(R) and isprimeforsure(R,factolimit,hardness,witlimit,triallimit)
                if not inequalityachieved:
                    Rminusone = R - 1
                    Rminustwo = R - 2
                    RFfacto,RR = pollardsrho(Rminusone,factolimit,hardness)
                    pseudoprimes = pseudoprimes.union(set(RFfacto))
                    RF = Rminusone // RR
                    for p in RFfacto:
                        witnessfound = False
                        for _ in range(witlimit):
                            a = random.randint(2,Rminustwo)
                            if pow(a,Rminusone,R) == 1 == math.gcd(pow(a,Rminusone // p,R) - 1,R):
                                witnessfound = True
                                break
                        if not witnessfound:
                            RF = 1
                            break
                    B = RF + 1
                    if B * B > R:
                        inequalityachieved = True
                    else:
                        if B == 2 and R & 1:
                            B = 3
                        if B == 3 and R % 3:
                            B = 5
                        if B == 4:
                            B = 5
                        if B > 4:
                            Bmodsix = B % 6
                            if Bmodsix < 2:
                                B += 1 - Bmodsix
                                onemodsix = True
                            else:
                                B += 5 - Bmodsix
                                onemodsix = False
                            for _ in range(triallimit):
                                if not R % B:
                                    break
                                B += 2 + (int(onemodsix) << 1)
                                onemodsix = not onemodsix
                        inequalityachieved = n < (B * F + 1) * (((F * F) << 1) + (r - B) * F + 1)
                if inequalityachieved:
                    square = r * r - (s << 3)
                    root = round(math.sqrt(square))
                    result = not s or root * root != square
            if inequalityachieved:
                for pseudoprime in pseudoprimes:
                    if not isprimeforsure(pseudoprime,factolimit,hardness,witlimit,triallimit):
                        return False
                return result
        factolimit *= 10
def lenstrasecm(n,limit,hardness):
    if n in dejavu:
        facto,leftover = dejavu[n]
        return facto.copy(),leftover
    if isprime(n):
        dejavu[n] = ({n:1},1)
        return {n:1},1
    nminustwo = n - 2
    x = random.randint(2,nminustwo)
    y = random.randint(2,nminustwo)
    a = random.randint(2,nminustwo)
    for number in [x,y,a]:
        factor = math.gcd(number,n)
        if factor > 1:
            break
    if factor == 1:
        factorfound = False
        for multiplier in range(2,limit):
            doubledx = x
            doubledy = y
            x = n
            y = n
            while True:
                if multiplier & 1:
                    if y == n:
                        x = doubledx
                        y = doubledy
                    elif doubledy < n:
                        if x == doubledx:
                            if (y + doubledy) % n:
                                snumerator = (3 * x * x + a) % n
                                sdenominator = (y << 1) % n
                                greatestcd = math.gcd(snumerator,sdenominator)
                                snumerator //= greatestcd
                                sdenominator //= greatestcd
                                factor,s = eea(sdenominator,n)
                                if 1 < factor < n:
                                    factorfound = True
                                    break
                                if factor == n:
                                    x = n
                                    y = n
                                else:
                                    s = (snumerator * s) % n
                                    x = (s * s - (x << 1)) % n
                                    y = (s * (doubledx - x) - y) % n
                            else:
                                x = n
                                y = n
                        else:
                            snumerator = (y - doubledy) % n
                            sdenominator = (x - doubledx) % n
                            greatestcd = math.gcd(snumerator,sdenominator)
                            snumerator //= greatestcd
                            sdenominator //= greatestcd
                            factor,s = eea(sdenominator,n)
                            if 1 < factor < n:
                                factorfound = True
                                break
                            if factor == n:
                                x = n
                                y = n
                            else:
                                s = (snumerator * s) % n
                                newx = (s * s - x - doubledx) % n
                                y = (s * (x - newx) - y) % n
                                x = newx
                multiplier >>= 1
                if not multiplier:
                    break
                if doubledy < n:
                    snumerator = (3 * doubledx * doubledx + a) % n
                    sdenominator = (doubledy << 1) % n
                    greatestcd = math.gcd(snumerator,sdenominator)
                    snumerator //= greatestcd
                    sdenominator //= greatestcd
                    factor,s = eea(sdenominator,n)
                    if 1 < factor < n:
                        factorfound = True
                        break
                    if factor == n:
                        doubledx = n
                        doubledy = n
                    else:
                        s = (snumerator * s) % n
                        newx = (s * s - (doubledx << 1)) % n
                        doubledy = (s * (doubledx - newx) - doubledy) % n
                        doubledx = newx
            if factorfound:
                break
    if factor in [1,n]:
        return {},n
    firstfacto,firstleftover = lenstrasecm(factor,limit,hardness)
    secondfacto,secondleftover = lenstrasecm(n // factor,limit,hardness)
    for prime in secondfacto:
        if prime in firstfacto:
            firstfacto[prime] += secondfacto[prime]
        else:
            firstfacto[prime] = secondfacto[prime]
    leftover = firstleftover * secondleftover
    dejavu[n] = (firstfacto.copy(),leftover)
    if (leftover == 1 and len(firstfacto) > 1 and sorted(firstfacto)[-2] > hardness) or (leftover > 1 and firstfacto and sorted(firstfacto)[-1] > hardness):
        facto = []
        for prime in firstfacto:
            facto += [str(prime) + "^" + str(firstfacto[prime])]
        factofile.write(" ".join((str(n),".".join(facto),str(leftover))) + "\n")
        factofile.flush()
    return firstfacto,leftover
def boundforexclusion(S):
    efficiencies = []
    abundancies = []
    bounds = []
    index = 0
    prime = 1
    abundancy = 1
    result = 0
    while abundancy < 2:
        prime += 2
        while prime in S or not isprime(prime):
            prime += 2
        maxefficiency = math.log((prime + 1) / prime) / math.log(prime)
        while index < len(efficiencies) and efficiencies[index] > maxefficiency:
            abundancy *= abundancies[index]
            if abundancy > 2:
                break
            result += bounds[index]
            index += 1
        sumofdivisors = 1
        primepower = 1
        divisible = True
        while divisible:
            primepower *= prime
            sumofdivisors += primepower
            divisible = not (sumofdivisors & 3)
            for forbidden in S:
                divisible = divisible or not (sumofdivisors % forbidden)
        efficiency = math.log(sumofdivisors / primepower) / math.log(primepower)
        jindex = index
        while jindex < len(efficiencies) and efficiencies[jindex] > efficiency:
            jindex += 1
        efficiencies = efficiencies[:jindex] + [efficiency] + efficiencies[jindex:]
        abundancies = abundancies[:jindex] + [prime / (prime - 1)] + abundancies[jindex:]
        bounds = bounds[:jindex] + [math.log(primepower,10)] + bounds[jindex:]
    return result
# 182952582665860380289038282589894954917657510496737584271686202133278382580291760821627874531484653786125242932372079118234502184940644796682501348468282295310929202477911070423776521538882872953941654188478922668790235834229540102875853132389518892443244411631091579022004506760454659199182952911734582485153630233923813171938753603
# 18295258266586038028903828258989495491765751049673758427168620213327838258029176082162787453148465378612524293237207911823450218494064479668250134846828229531092920247791107042377652153888287295394165418847892266879023583422954010287585313238951889244324441163109157902200450676045465919918295291173458248515363023392381317193884837
def findunsatisfiableprimes(Nbound):
    primebound = 3 * Nbound
    lo = 10 ** ((len(str(primebound)) - 1) // 3)
    hi = lo * 10
    while lo < hi - 1:
        mid = (lo + hi) >> 1
        if mid * mid * mid > primebound:
            hi = mid
        else:
            lo = mid
    primebound = hi
    prime = (primebound + 1) >> 1
    lo = 10 ** ((len(str(prime)) - 1) >> 1)
    hi = lo * 10
    while lo < hi - 1:
        mid = (lo + hi) >> 1
        if mid * mid > prime:
            hi = mid
        else:
            lo = mid
    prime = lo
    exponentbound = int(math.log(Nbound,3))
    smallprimes = generateprimes(exponentbound)[1:]
    counter = 0
    while True:
        prime //= 10
        prime += 1 - (prime & 1)
        searching = True
        while searching:
            if isprime(prime):
                counter += 1
                if not counter % 10:
                    print("Status:",prime)
                works = True
                primeminusone = prime - 1
                for smallprime in smallprimes:
                    works = works and bool(primeminusone % smallprime)
                    if not works:
                        break
                if works:
                    otherprime = ((prime * prime) << 1) - 1
                    increment = (otherprime << 1) + 2
                    wontwork = True
                    while wontwork and otherprime < primebound:
                        if isprime(otherprime):
                            N = prime * prime
                            oppo = (otherprime + 1) // N
                            parity = True
                            div,mod = divmod(oppo,prime)
                            while not mod:
                                oppo = div
                                N *= prime
                                parity = not parity
                                div,mod = divmod(oppo,prime)
                            if parity:
                                div,mod = divmod((N * prime - 1) // (prime - 1),otherprime)
                                if mod:
                                    N *= otherprime
                                    opmo = otherprime - 1
                                    opmobackup = opmo
                                    primes = []
                                    exponents = []
                                    for smallprime in smallprimes:
                                        div,mod = divmod(opmo,smallprime)
                                        if not mod:
                                            primes += [smallprime]
                                            exponent = 1
                                            opmo = div
                                            div,mod = divmod(opmo,smallprime)
                                            while not mod:
                                                exponent += 1
                                                opmo = div
                                                div,mod = divmod(opmo,smallprime)
                                            exponents += [exponent]
                                    opmt = otherprime - 2
                                    pseudoroot = random.randint(2,opmt)
                                    aintroot = False
                                    for prim in primes:
                                        aintroot = pow(pseudoroot,opmobackup // prim,otherprime) == 1
                                        if aintroot:
                                            break
                                    while aintroot:
                                        pseudoroot = random.randint(2,opmt)
                                        aintroot = False
                                        for prim in primes:
                                            aintroot = pow(pseudoroot,opmobackup // prim,otherprime) == 1
                                            if aintroot:
                                                break
                                    lenprimes = len(primes)
                                    currexps = [0] * lenprimes
                                    while wontwork:
                                        index = lenprimes - 1
                                        while index > -1 and currexps[index] == exponents[index]:
                                            currexps[index] = 0
                                            index -= 1
                                        if index == -1:
                                            break
                                        currexps[index] += 1
                                        exponent = 1
                                        for index in range(lenprimes):
                                            exponent *= primes[index] ** currexps[index]
                                        if exponent <= exponentbound:
                                            residues = []
                                            residue = pow(pseudoroot,opmobackup // exponent,otherprime)
                                            currres = residue
                                            for _ in range(exponent - 1):
                                                residues += [currres]
                                                currres = (currres * residue) % otherprime
                                            residues.sort()
                                            multiplier = 0
                                            withinbounds = True
                                            while wontwork and withinbounds:
                                                for residue in residues:
                                                    otherotherprime = multiplier * otherprime + residue
                                                    if otherotherprime > primebound or N * (otherotherprime ** (exponent - 1)) > Nbound:
                                                        withinbounds = False
                                                        break
                                                    if isprime(otherotherprime) and pow(otherotherprime,exponent,otherprime * otherprime) > 1:
                                                        wontwork = False
                                                        break
                                                multiplier += 1
                                elif div % otherprime:
                                        wontwork = False
                        otherprime += increment
                    if wontwork:
                        print("|")
                        print("|")
                        print("V")
                        print(prime)
                        print("^")
                        print("|")
                        print("|")
                        searching = False
            prime += 2
def proofsubroutine(exactfacto,factosofar,special,composite,currprime,currexp,maxexponent,forbiddens,linenum,level,bound,smallprimes,limit,increasefactor,hardness):
    exactfacto[currprime] = currexp
    if currexp == 1:
        special = currprime
    btwo = int(2 * currexp * math.log(currprime,10))
    if btwo >= bound:
        strlinenum = str(linenum)
        print(strlinenum + ":" + " " * (5 - len(strlinenum) + (level << 1)) + str(currprime) + "^" + str(currexp) + ", B2 " + str(btwo))
        exactfacto.pop(currprime)
        return linenum + 1,False
    if currexp > maxexponent:
        strlinenum = str(linenum)
        print(strlinenum + ":" + " " * (5 - len(strlinenum) + (level << 1)) + str(currprime) + "^" + str(currexp) + ", E " + str(maxexponent))
        exactfacto.pop(currprime)
        return linenum + 1,False
    if currprime in factosofar:
        merged = True
        oldexp = factosofar[currprime]
        factosofar[currprime] = max(oldexp,currexp)
    else:
        merged = False
        factosofar[currprime] = currexp
    bthree = 0
    hisingle = 0
    for prime in factosofar:
        exponent = factosofar[prime]
        if exponent == 1 and prime & 3 == 1:
            hisingle = max(hisingle,prime)
        bthree += (exponent + (exponent & 1)) * math.log(prime,10)
    if special:
        bthree -= math.log(special,10)
    elif hisingle:
        bthree -= math.log(hisingle,10)
    bthree = int(bthree)
    if bthree >= bound:
        strlinenum = str(linenum)
        print(strlinenum + ":" + " " * (5 - len(strlinenum) + (level << 1)) + str(currprime) + "^" + str(currexp) + ", B3 " + str(bthree))
        if merged:
            factosofar[currprime] = oldexp
        else:
            factosofar.pop(currprime)
        exactfacto.pop(currprime)
        return linenum + 1,False
    sumofdivisors = ((currprime ** (currexp + 1)) - 1) // (currprime - 1)
    if not sumofdivisors & 1:
        sumofdivisors >>= 1
    for prime in forbiddens:
        if not sumofdivisors % prime:
            strlinenum = str(linenum)
            print(strlinenum + ":" + " " * (5 - len(strlinenum) + (level << 1)) + str(currprime) + "^" + str(currexp) + " => " + str(prime) + "..., D")
            if merged:
                factosofar[currprime] = oldexp
            else:
                factosofar.pop(currprime)
            exactfacto.pop(currprime)
            return linenum + 1,True
    oldfacto = {}
    abundancy = 1
    losingle = 0
    sumfacto = {}
    abundancyfacto = {}
    bone = 1
    hisingle = 0
    for prime in factosofar:
        if not sumofdivisors % prime:
            newexp = 1
            sumofdivisors //= prime
            while not sumofdivisors % prime:
                newexp += 1
                sumofdivisors //= prime
            if newexp > factosofar[prime]:
                oldfacto[prime] = factosofar[prime]
                factosofar[prime] = newexp
            sumfacto[prime] = newexp
        exponent = factosofar[prime]
        if exponent == 1 and prime & 3 == 1:
            if not losingle or losingle > prime:
                losingle = prime
            hisingle = max(hisingle,prime)
        exponent += exponent & 1
        abundancyfacto[prime] = exponent
        abundancy *= (prime - 1 / (prime ** exponent)) / (prime - 1)
        bone *= prime ** exponent
    if special:
        abundancy *= 1 - 1 / (special * special + special + 1)
        abundancyfacto[special] = 1
    elif losingle:
        abundancy *= 1 - 1 / (losingle * losingle + losingle + 1)
        abundancyfacto[losingle] = 1
    if abundancy > 2:
        strlinenum = str(linenum)
        sumstring = ""
        for prime in sumfacto:
            sumstring += str(prime) + "^" + str(sumfacto[prime]) + "."
        if sumofdivisors == 1:
            sumstring = sumstring[:-1] + ","
        else:
            sumstring += "..,"
        abundstring = ""
        for prime in abundancyfacto:
            abundstring += str(prime) + "^" + str(abundancyfacto[prime]) + "."
        print(strlinenum + ":" + " " * (5 - len(strlinenum) + (level << 1)) + str(currprime) + "^" + str(currexp) + " => " + sumstring + " S " + abundstring[:-1])
        for prime in oldfacto:
            factosofar[prime] = oldfacto[prime]
        if merged:
            factosofar[currprime] = oldexp
        else:
            factosofar.pop(currprime)
        exactfacto.pop(currprime)
        return linenum + 1,True
    if special:
        abundancy *= 1 + 1 / (special * special + special)
        abundancyfacto[special] = 2
    elif losingle:
        abundancy *= 1 + 1 / (losingle * losingle + losingle)
        abundancyfacto[losingle] = 2
    newprimes = set()
    leftover = 1
    if sumofdivisors > 1:
        for prime in smallprimes:
            if prime * prime > sumofdivisors:
                newprimes.add(sumofdivisors)
                factosofar[sumofdivisors] = 1
                if sumofdivisors & 3 == 1:
                    if not losingle or losingle > sumofdivisors:
                        losingle = sumofdivisors
                    hisingle = max(hisingle,sumofdivisors)
                abundancy *= 1 + (sumofdivisors + 1) / sumofdivisors / sumofdivisors
                abundancyfacto[sumofdivisors] = 2
                bone *= sumofdivisors * sumofdivisors
                sumfacto[sumofdivisors] = 1
                sumofdivisors = 1
            if not sumofdivisors % prime:
                newprimes.add(prime)
                factosofar[prime] = 1
                sumofdivisors //= prime
                while not sumofdivisors % prime:
                    factosofar[prime] += 1
                    sumofdivisors //= prime
                exponent = factosofar[prime]
                if exponent == 1 and prime & 3 == 1:
                    if not losingle or losingle > prime:
                        losingle = prime
                    hisingle = max(hisingle,prime)
                sumfacto[prime] = exponent
                exponent += exponent & 1
                abundancy *= (prime - 1 / (prime ** exponent)) / (prime - 1)
                abundancyfacto[prime] = exponent
                bone *= prime ** exponent
            if sumofdivisors == 1:
                break
        if special:
            abundancy *= 1 - 1 / (special * special + special + 1)
            abundancyfacto[special] = 1
        elif losingle:
            abundancy *= 1 - 1 / (losingle * losingle + losingle + 1)
            abundancyfacto[losingle] = 1
        if abundancy > 2:
            strlinenum = str(linenum)
            sumstring = ""
            for prime in sumfacto:
                sumstring += str(prime) + "^" + str(sumfacto[prime]) + "."
            if sumofdivisors == 1:
                sumstring = sumstring[:-1] + ","
            else:
                sumstring += "..,"
            abundstring = ""
            for prime in abundancyfacto:
                abundstring += str(prime) + "^" + str(abundancyfacto[prime]) + "."
            print(strlinenum + ":" + " " * (5 - len(strlinenum) + (level << 1)) + str(currprime) + "^" + str(currexp) + " => " + sumstring + " S " + abundstring[:-1])
            for prime in newprimes:
                factosofar.pop(prime)
            for prime in oldfacto:
                factosofar[prime] = oldfacto[prime]
            if merged:
                factosofar[currprime] = oldexp
            else:
                factosofar.pop(currprime)
            exactfacto.pop(currprime)
            return linenum + 1,True
        if special:
            abundancy *= 1 + 1 / (special * special + special)
            abundancyfacto[special] = 2
        elif losingle:
            abundancy *= 1 + 1 / (losingle * losingle + losingle)
            abundancyfacto[losingle] = 2
        if sumofdivisors > 1:
            facto,leftover = lenstrasecm(sumofdivisors,limit,hardness)
            limb = limit * 10
            newlimit = limit
            while not facto and newlimit < limb:
                newlimit = round(newlimit * increasefactor)
                facto,leftover = lenstrasecm(sumofdivisors,newlimit,hardness)
            if special:
                bone //= special
            elif hisingle:
                bone //= hisingle
            lcm = bone * composite // math.gcd(bone,composite)
            if not newprimes and lcm * leftover // math.gcd(lcm,leftover) < 10 ** bound:
                while not facto:
                    newlimit = round(newlimit * increasefactor)
                    facto,leftover = lenstrasecm(sumofdivisors,newlimit,hardness)
            if special:
                bone *= special
            elif hisingle:
                bone *= hisingle
            for prime in facto:
                exponent = facto[prime]
                factosofar[prime] = exponent
                newprimes.add(prime)
                if exponent == 1 and prime & 3 == 1:
                    if not losingle or losingle > prime:
                        losingle = prime
                    hisingle = max(hisingle,prime)
                sumfacto[prime] = exponent
                exponent += exponent & 1
                abundancy *= (prime - 1 / (prime ** exponent)) / (prime - 1)
                abundancyfacto[prime] = exponent
                bone *= prime ** exponent
            if special:
                abundancy *= 1 - 1 / (special * special + special + 1)
                abundancyfacto[special] = 1
            elif losingle:
                abundancy *= 1 - 1 / (losingle * losingle + losingle + 1)
                abundancyfacto[losingle] = 1
            if abundancy > 2:
                strlinenum = str(linenum)
                sumstring = ""
                for prime in sumfacto:
                    sumstring += str(prime) + "^" + str(sumfacto[prime]) + "."
                if sumofdivisors == 1:
                    sumstring = sumstring[:-1] + ","
                else:
                    sumstring += "..,"
                abundstring = ""
                for prime in abundancyfacto:
                    abundstring += str(prime) + "^" + str(abundancyfacto[prime]) + "."
                print(strlinenum + ":" + " " * (5 - len(strlinenum) + (level << 1)) + str(currprime) + "^" + str(currexp) + " => " + sumstring + " S " + abundstring[:-1])
                for prime in newprimes:
                    factosofar.pop(prime)
                for prime in oldfacto:
                    factosofar[prime] = oldfacto[prime]
                if merged:
                    factosofar[currprime] = oldexp
                else:
                    factosofar.pop(currprime)
                exactfacto.pop(currprime)
                return linenum + 1,True
    if special:
        bone //= special
    elif hisingle:
        bone //= hisingle
    composite *= leftover // math.gcd(composite,leftover)
    bone = int(math.log(bone * composite // math.gcd(bone,composite),10))
    strlinenum = str(linenum)
    sumstring = ""
    for prime in sumfacto:
        sumstring += str(prime) + "^" + str(sumfacto[prime]) + "."
    sumstring = sumstring[:-1]
    if leftover > 1:
        if sumfacto:
            sumstring += "."
        sumstring += "n"
    print(strlinenum + ":" + " " * (5 - len(strlinenum) + (level << 1)) + str(currprime) + "^" + str(currexp) + " => " + sumstring + ", B1 " + str(bone))
    linenum += 1
    if bone >= bound:
        for prime in newprimes:
            factosofar.pop(prime)
        for prime in oldfacto:
            factosofar[prime] = oldfacto[prime]
        if merged:
            factosofar[currprime] = oldexp
        else:
            factosofar.pop(currprime)
        exactfacto.pop(currprime)
        return linenum,True
    proofin = True
    if special:
        minexp = 1000000
        for prime in newprimes.union(set(sumfacto).difference(set(exactfacto))):
            expbound = int(bound * math.log(10,prime) / 2)
            maxexp = 0
            for usedprime in exactfacto:
                sumofdivisors = ((usedprime ** (exactfacto[usedprime] + 1)) - 1) // (usedprime - 1)
                while not sumofdivisors % prime:
                    maxexp += 1
                    sumofdivisors //= prime
                if maxexp >= expbound:
                    break
            increment = prime << 1
            otherprime = increment + 1
            exp = prime - 1
            while maxexp < expbound and (exp << 1) * math.log(otherprime,10) < bound:
                while otherprime in exactfacto or not isprime(otherprime):
                    otherprime += increment
                hiexp = 0
                while (exp << 1) * math.log(otherprime,10) < bound:
                    sumofdivisors = ((otherprime ** (exp + 1)) - 1) // (otherprime - 1)
                    exponent = 0
                    while not sumofdivisors % prime:
                        exponent += 1
                        sumofdivisors //= prime
                    hiexp = max(hiexp,exponent)
                    exp += increment
                maxexp += hiexp
                otherprime += increment
                exp = prime - 1
            if maxexp < expbound:
                exponents = []
                for exponent in range(3,int(bound * math.log(10,9)) + 2,2):
                    if prime % exponent == 1:
                        exponents += [exponent]
                if exponents:
                    primebound = int(10 ** (bound / (exponents[0] - 1) / 2))
                    if primebound > smallprimes[-1]:
                        maxexp = expbound
                    else:
                        for smallprime in smallprimes:
                            if smallprime > primebound:
                                break
                            if smallprime not in exactfacto and smallprime % prime > 1:
                                order = 0
                                for exponent in exponents:
                                    if pow(smallprime,exponent,prime) == 1:
                                        order = exponent
                                        break
                                if order:
                                    hiexp = 0
                                    for exp in range(order,int(bound * math.log(10,smallprime) / 2) + 2,order << 1):
                                        sumofdivisors = ((smallprime ** exp) - 1) // (smallprime - 1)
                                        exponent = 0
                                        while not sumofdivisors % prime:
                                            exponent += 1
                                            sumofdivisors //= prime
                                        hiexp = max(hiexp,exponent)
                                    maxexp += hiexp
                                    if maxexp >= expbound:
                                        break
            maxexp = min(maxexp,expbound)
            if maxexp < minexp:
                minexp = maxexp
                newprime = prime
    else:
        newprime = max(newprimes.union(set(sumfacto).difference(set(exactfacto))))
        minexp = int(bound * math.log(10,newprime) / 2)
    lowestexp = factosofar[newprime]
    if not special and newprime & 3 == 1 and lowestexp == 1:
        linenum,proofin = proofsubroutine(exactfacto,factosofar,special,composite,newprime,1,minexp,forbiddens,linenum,level + 1,bound,smallprimes,limit,increasefactor,hardness)
    newexp = lowestexp + (lowestexp & 1)
    while proofin:
        linenum,proofin = proofsubroutine(exactfacto,factosofar,special,composite,newprime,newexp,minexp,forbiddens,linenum,level + 1,bound,smallprimes,limit,increasefactor,hardness)
        newexp += 2
        while not isprime(newexp + 1):
            newexp += 2
    for prime in newprimes:
        factosofar.pop(prime)
    for prime in oldfacto:
        factosofar[prime] = oldfacto[prime]
    if merged:
        factosofar[currprime] = oldexp
    else:
        factosofar.pop(currprime)
    exactfacto.pop(currprime)
    return linenum,True
def proof(perfectbound,primebound,limit,increasefactor,hardness,factorbase):
    #if boundforexclusion(factorbase) < perfectbound:
     #   print("Factor bsse too small!")
    #else:
    forbiddens = []
    linenum = 1
    smallprimes = generateprimes(primebound)[1:]
    for prime in factorbase:
        proofin = True
        if prime & 3 == 1:
            linenum,proofin = proofsubroutine({},{},0,1,prime,1,1000000,forbiddens,linenum,0,perfectbound,smallprimes,limit,increasefactor,hardness)
        exp = 2
        while proofin:
            linenum,proofin = proofsubroutine({},{},0,1,prime,exp,1000000,forbiddens,linenum,0,perfectbound,smallprimes,limit,increasefactor,hardness)
            exp += 2
            while not isprime(exp + 1):
                exp += 2
        forbiddens += [prime]
#https://uwaterloo.ca/math-faculty-computing-facility/services/service-catalogue-research-linux/research-linux-server-hardware
