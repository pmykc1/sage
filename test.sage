def findSi(PolyMatrix, M):
    polymatrixiter = 0
    K = M.base_field()
    n = M.rank()
    m = M.degree()
    i=1
    Si = zero_matrix(K,n,m)
    while i <= n:
        Si[i-1] = PolyMatrix[polymatrixiter]
        polymatrixiter+=1
        while ((K**m).span(Si)).rank() < i:
            Si[i-1] = PolyMatrix[polymatrixiter]
            polymatrixiter+=1
        i+=1
    return Si

def Si_reduce(M,Q):                                
    n = M.rank()                                 
    m = M.degree()                                                               
    K = M.base_field()                  
    Ok = K.ring_of_integers()                                      
    d = K.degree()                                                 
    intversion = zero_matrix(QQ,n*d,m*d)                                                                           
    for basis in range(n*d):                                                                                       
        for entry in range(m*d):                                                                                   
            intversion[basis,entry]=(M.basis()[floor(basis/d)][floor(entry/d)]*Ok.basis()[basis%d]).list()[entry%d]
    denominator = intversion.denominator()
    intversion = intversion*denominator             
    intversion = qLLL(intversion,Q)
    PolyMatrix = zero_matrix(K,n*d,m)
    for basis in range(n*d):  
        for entry in range(m):                                    
            value = 0                                             
            for i in range(d):                                    
                value += intversion[basis,entry*d+i]*Ok.basis()[i]
            PolyMatrix[basis,entry]=value
    PolyMatrix = basis_sort(PolyMatrix,Q)     
    Si = findSi(PolyMatrix,M)                           
    Si = Si/denominator                                 
    T = matrix([M.coordinates(v) for v in Si])          
    H,ideals = trial_bpc_hnf(T,[Ok*1 for i in range(n)])
    U=~H*T               
    A = matrix(M.basis()) 
    B=U*A                        
    for i in range(n):           
        ideal = ~ideals[i]       
        x=ideal.gens_reduced()[0]
        ideals[i]=ideal/x
        B[i]*=x        
        reset('x')   
    B = basis_sort(B,Q)
    return B,ideals


def gso(B,Q):                                                                                                                                     
    Bstar = copy(B)                                                                                          
    u=zero_matrix(RR,B.rank(),B.rank())                                                                            
    for i in range(B.rank()):                                                                                             
        for j in range(i):                                                                                   
            u[i,j] = (fieldtoint(B[i])*Q*fieldtoint(Bstar[j]).transpose())[0]/(fieldtoint(Bstar[j])*Q*fieldtoint(Bstar[j]).transpose())[0]                     
            Bstar[i]-=Rational(u[i,j])*Bstar[j]                                                                     
    return Bstar, u  


def compare_bases(A,B,Q):                                                                                                                         
    A = basis_sort(A,Q)                                                                                        
    B = basis_sort(B,Q)                                                                                        
    string = ""                                                                                              
    for i in range(A.rank()):                                                                                
        norm1 = (fieldtoint(A[i])*Q*fieldtoint(A[i]).transpose()).list()[0]
        norm2 = (fieldtoint(B[i])*Q*fieldtoint(B[i]).transpose()).list()[0]
        if norm1>norm2:                                                                                      
            string+="B better than A on vector "+str(i)+", "                                                 
        if norm1==norm2:                                                                                     
            string+="B as good as A on vector "+str(i)+", "                                               
        if norm1<norm2:                                                                                   
            string+="B worse than A on vector "+str(i)+", "                                               
    return string   


def basis_sort(L,Q):                                                                                                                              
    v = zero_vector(RR,L.rank())                                                                             
    sortedL = copy(L)                                                                                        
    for toput in range(L.rank()):                                                                            
        norm = (fieldtoint(L[toput])*Q*fieldtoint(L[toput]).transpose()).list()[0]
        place = 0                                                                                            
        while v[place]!=0 and norm>v[place]:                                                                 
            place+=1                                                                                         
        temp = v[place]                                                                                      
        v[place] = norm                                                                                      
        templ = sortedL[place]                                                                            
        sortedL[place] = L[toput]                                                                         
        while temp!=0:                                                                                    
            place+=1                                                                                      
            temp2 = v[place]                                                                              
            v[place] = temp                                                                               
            temp = temp2                                                                                  
            templ2 = sortedL[place]                                                                       
            sortedL[place] = templ                                                                        
            templ = templ2                                                                                
    return sortedL            
    
def T2_norm(x,y):                                                                                                                               
    value = 0                                    
    deltas = (x.parent()).embeddings(CC)                                                                     
    for delta in deltas:                                                                                           
        value+=(delta(x))*conjugate(delta(y))                                                                             
    return value     


def size_reduce(B,ideals,Q):                                                                                                                      
    returnB = copy(B)                                                                                        
    for i in range(B.rank()):                                                                                      
        j = i-1                                                                                                           
        while j>=0:                                                                                          
            bstar, u = gso(returnB,Q)                                                                          
            returnB[i]-=round(u[i,j])*returnB[j]                                                                    
            j-=1                                                                                             
    return returnB     
      

def qLLL(L,Q):           
    returnL = copy(L)
    flag = True
    while flag == True:
        Ldash,u = qgso(returnL,Q)
        n = returnL.rank()
        for i in range(1,n):
            for j in reversed(range(0,i)):
                cij = round((returnL[i]*Q*Ldash[j])/(Ldash[j]*Q*Ldash[j]))

                returnL[i]-=cij*returnL[j]
        Ldash,u = qgso(returnL,Q)
        flag = False
        for i in range(n-1):
            if (3/4)*Ldash[i]*Q*Ldash[i] > (u[i+1,i]*Ldash[i]+Ldash[i+1])*Q*(u[i+1,i]*Ldash[i]+Ldash[i+1]):
                temp = returnL[i]
                returnL[i] = returnL[i+1]
                returnL[i+1] = temp
                flag = True
    return returnL


def qgso(B,Q):                                                            
                                                                       
    Bstar = zero_matrix(QQ,B.rank(),B[0].degree())                        
                                                              
    u=zero_matrix(RR,B.rank(),B.rank())                                   
                            
    for i in range(B.rank()):                                             
        Bstar[i]=copy(B[i])                                               
                                                                          
        for j in range(i):                                                
                                                                          
            u[i,j] = (B[i]*Q*Bstar[j])/(Bstar[j]*Q*Bstar[j])              
                                                                          
            Bstar[i]-=Rational(u[i,j])*Bstar[j]                           
                                                                          
    return Bstar, u  


def T2normQ(K):
    d = K.degree()
    Q = zero_matrix(RR,d,d)
    Ok = K.ring_of_integers()
    for i in range(d):
        for j in range(d):
            first = Ok.basis()[i]
            second = Ok.basis()[j]
            Q[i,j]=(T2_norm(K(first+second),K(first+second))-T2_norm
(K(first),K(first))-T2_norm(K(second),K(second)))/2
    return Q

 
def fieldtoint(v):
    intlist = []
    for entry in v:
        intlist+=entry.list()
    return matrix([intlist])
    
def trial_bpc_hnf(T,startideals):    
    A = copy(T)                        
    ideals = copy(startideals)         
    K = ideals[0].number_field()       
    n = A.rank()                       
    k = A[0].degree()                  
    i = 0                            
    j = 0                                    
    while i<=n-1:                                
        m = j                                  
        while m<n and A[i,m]==0:               
            m+=1                                
        if m==n:                                 
            return A, ideals                    
        if m>j:                                 
            temp = A.column(m)                  
            A.set_column(m,A.column(j))         
            A.set_column(j,temp)                
            temp = ideals[m]                    
            ideals[m] = ideals[j]               
            ideals[j] = temp               
            m = j                              
        aij = A[i,j]                           
        A.set_column(j,A.column(j)/aij)  
        ideals[j]*=aij                                                                           
        while m<n-1:                                                                               
            m+=1                                                                                 
            if A[i,m]!=0:                                                                        
                aim = A[i,m]                                                                     
                delta = aim*ideals[m]+ideals[j]                                                  
                uideal = aim*ideals[m]*~delta                                                    
                videal = ideals[j]*~delta                                                        
                v = videal.element_1_mod(uideal) 
                u = (1-v)/aim
                Am = A.column(m)                                                                   
                Aj = A.column(j)                                                                   
                A.set_column(m,Am-aim*Aj)                                                          
                A.set_column(j,u*Am+v*Aj)                                                          
                ideals[m]*=ideals[j]*~delta                                                        
                ideals[j]=delta                                                                    
        m=j-1                                                                                    
        while m >= 0:                                                                            
            domain = ideals[m]*~ideals[j]                                                        
            denominator = domain.denominator().gens_reduced()[0]                                 
            q = A[i,m]*denominator-(domain*denominator).small_residue(A[i,m]*denominator)        
            A.set_column(m,A.column(m)-q*A.column(j))                                            
            m-=1                                                                                 
        i+=1                                                                                     
        j+=1                                                                                     
                                                                                                 
    return A, ideals 

def relative_POLRED(K,f):
    L.<epsilon> = K.extension(f)
    Ol = L.ring_of_integers()
    n = len(Ol.basis())
    basisnums = zero_matrix(QQ,n,L.absolute_degree())
    for i in range(n):
        for j in range(L.absolute_degree()):
            basisnums[i,j] = Ol.basis()[i].list()[j%L.relative_degree()].list()[floor(j/L.relative_degree())]
    optimisedbasis = zero_matrix(ZZ,n,L.absolute_degree())
    for i in range(n):
        for j in range(L.absolute_degree()):
            optimisedbasis[i,j]=basisnums[i,j]*basisnums.denominator()
    optimisedbasis = optimisedbasis.echelon_form()/basisnums.denominator()
    basis = copy(Ol.basis())
    for entry in range(n):
        basis[entry]=0
        for exp in range(L.absolute_degree()):
            basis[entry]+=optimisedbasis[entry,exp]*theta^(floor(exp/L.relative_degree()))*epsilon^(exp%L.relative_degree())
    tracematrix = identity_matrix(RR,n)
    for i in range(n):
        for j in range(n):
            tracematrix[i,j]=T2_norm(L(basis[i]),L(basis[j])).real()
    d = K.degree()
    nlattice = n*d
    Q = zero_matrix(RR,nlattice,nlattice)
    for row in range(nlattice):
        for column in range(nlattice):
            Q[row,column]=T2normQ(K)[row%d,column%d]*tracematrix[row/d,column/d]
    Ok = K.ring_of_integers()
    M = (K^(n)).span_of_basis(identity_matrix(ZZ,n),base_ring=Ok)
    coeffs = Si_reduce(M,Q)[0]
    polys = [0 for i in range(coeffs.rank())]
    for i in range(coeffs.rank()):
        for coeff in range(n):
            polys[i]+=L(coeffs[i,coeff])*basis[coeff]
    return polys
