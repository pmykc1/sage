#findSi takes a lattice basis A and a large number of vectors in the lattice vectorpool, and returns a full-rank linearly independent set
def findSi(vectorpool, A):
    vectoriter = 0
    K = A[0,0].parent()
    n = A.rank()
    m = A[0].degree()
    i=1
    Si = zero_matrix(K,n,m)
    while i <= n:
        #set the next empty Si entry to a vector
        Si[i-1] = vectorpool[vectoriter]
        vectoriter+=1
        #if the rank of Si hasn't increased then iterate until finding a vector which does increase it
        while Si.rank() < i:
            Si[i-1] = vectorpool[vectoriter]
            vectoriter+=1
        i+=1
    return Si


#gso finds the generalised gram-schmidt orthogonalised version of a lattice basis B and arbitrary quadratic form Q
def gso(B,Q):                                                                                                                                     
    Bstar = copy(B)                                                                                          
    u=zero_matrix(RR,B.rank(),B.rank())                                                                            
    for i in range(B.rank()):                                                                                             
        for j in range(i):                                                                                   
            u[i,j] = (fieldtoint(B[i])*Q*fieldtoint(Bstar[j]).transpose())[0]/(fieldtoint(Bstar[j])*Q*fieldtoint(Bstar[j]).transpose())[0]         
            #I cast to rational as the basis will always have rational base field            
            Bstar[i]-=Rational(u[i,j])*Bstar[j]                                                                     
    return Bstar, u  

#compare_bases compares two lattice bases A and B with arbitrary quadratic form Q. This helps verify that our method for finding short bases over
#number fields does indeed work. This method is not intended to be used in other contexts. It just says which basis vectors are longer/shorter
def compare_bases(A,B,Q):
    #comparing vector by vector so need to sort first 
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

#sorts a basis L from shortest to longest vector as defined by a given quadratic form Q
#This is a naive sort. It could be changed to the merge sort but in reality this is still quick enough.
#Alternatively sage may already have sorting methods for custom comparators but I could not find this.
def basis_sort(L,Q):           
    #v is a list of norms associated with the basis vectors. We store this so we don't have to repeatedly calculate norms.
    v = zero_vector(RR,L.rank())
    #sortedL is the sorted basis.                                                                             
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
    
#T2_norm gives the extended T2 value for two values x,y of the same field
def T2_norm(x,y):                                                                                                                               
    value = 0                                    
    deltas = (x.parent()).embeddings(CC)                                                                     
    for delta in deltas:                                                                                           
        value+=(delta(x))*conjugate(delta(y))                                                                             
    return value     


#size_reduce is step 7 of the LLL-reduction for lattices over number fields
def size_reduce(B,ideals,Q):                                                                                                                      
    returnB = copy(B)                                                                                        
    for i in range(B.rank()):                                                                                      
        j = i-1                                                                                                           
        while j>=0:                                                                                          
            bstar, u = gso(returnB,Q)                                                                          
            returnB[i]-=round(u[i,j])*returnB[j]                                                                    
            j-=1                                                                                             
    return returnB     
      
#qLLL is an LLL-reduction over integer lattices for arbitrary quadratic form Q
#This is in need of improvement as it follows the naive LLL algorithm from Henri Cohen's Course Book.
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

#qgso follows the same code as gso but with elements in integer (not number field) lattices
def qgso(B,Q):                                                            
    Bstar = zero_matrix(QQ,B.rank(),B[0].degree())                        
    u=zero_matrix(RR,B.rank(),B.rank())                                   
    for i in range(B.rank()):                                             
        Bstar[i]=copy(B[i])                                               
        for j in range(i):                                                
            u[i,j] = (B[i]*Q*Bstar[j])/(Bstar[j]*Q*Bstar[j])              
            Bstar[i]-=Rational(u[i,j])*Bstar[j]                           
    return Bstar, u  

#T2normQ gives the quadratic form matrix associated with the T2 norm
#This is done by simply considering the basis elements
def T2normQ(K):
    d = K.degree()
    Q = zero_matrix(RR,d,d)
    Ok = K.ring_of_integers()
    for i in range(d):
        for j in range(d):
            first = Ok.basis()[i]
            second = Ok.basis()[j]
            Q[i,j]=T2_norm(K(first),K(second))
    return Q

#In order to use a quadratic form matrix on an element in a field we regularly need to convert field vectors to integer vectors
def fieldtoint(v):
    intlist = []
    for entry in v:
        intlist+=entry.list()
    return matrix([intlist])
    

#relative_POLRED takes a base field K and polynomial f defining a field extension L, and finds a reduced polynomial defining the same extension.
#I have taken the primitive element of K to be given as theta, which is bad practice, but I don't know how to get the variable name from the field.
def relative_POLRED(K,f):
    L.<epsilon> = K.extension(f)
    #Big improvement possible - use K-basis for Ol not QQ-basis.
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
    #basis is now a reasonably small QQ-basis for Ol.
    tracematrix = identity_matrix(RR,n)
    for i in range(n):
        for j in range(n):
            tracematrix[i,j]=T2_norm(L(basis[i]),L(basis[j])).real()
    #we will use the tracematrix as the quadratic form. The real.() command is theoretically unnecessary but in reality rounding causes problems in its absence.
    d = K.degree()
    nlattice = n*d
    Q = zero_matrix(RR,nlattice,nlattice)
    t2Q = T2normQ(K)
    #Q is the big quadratic form created by combining the two smaller quadratic forms.
    for row in range(nlattice):
        for column in range(nlattice):
            Q[row,column]=t2Q[row%d,column%d]*tracematrix[row/d,column/d]
    #Si_reduce and size_reduce LLL-reduces the lattice with respect to Q
    coeffs,ideals = Si_reduce(identity_matrix(K,n),Q)
    coeffs = size_reduce(coeffs,ideals,Q)
    alternatives = [0 for i in range(coeffs.rank())]
    for i in range(coeffs.rank()):
        for coeff in range(n):
            alternatives[i]+=L(coeffs[i,coeff])*basis[coeff]
    polys = [L(alternative).minpoly() for alternative in alternatives]
    return polys

#bpc_hnf follows the naive algorithm from Cohen's advanced book.
def bpc_hnf(T,startideals):                                                           
    A = copy(T)                               
    K = A[0,0].parent()                       
    ideals = copy(startideals)                
    n = T.rank()                              
    k = A[0].degree()                         
    #step 1                                   
    i = 0                        
    j = 0                                      
    while i<k:                                 
    #step 2                                     
        m = j                                   
        while m<n and A[m,i]==0:                
            m+=1                                
        if m==n:                                
            return zero_matrix(K,n,k),U,ideals  
        if m>j:                                 
            temp = A[m]                         
            A[m]=A[j]                           
            A[j]=temp                                
            temp = ideals[m]                    
            ideals[m] = ideals[j]               
            ideals[j] = temp                    
            m=j                                                 
    #step 3                                                     
        aji = A[j,i]                                                                     
        A[j]/=aji                                                                          
        ideals[j]*=aji                                                                   
        #step 4                                                                          
        while m<n-1:                                                                     
            m+=1                                                                         
            if A[m,i]!=0:                                                                
            #step 5          
                ami = A[m,i]                  
                delta = ami*ideals[m]+ideals[j]
                uideal = ami*ideals[m]*~delta  
                videal = ideals[j]*~delta      
                v = videal.element_1_mod(uideal)
                u = (1-v)/ami                   
                Am = A[m]                       
                Aj = A[j]                       
                A[m]-=ami*Aj                    
                A[j]=u*Am+v*Aj                      
                ideals[m]*=ideals[j]*~delta     
                ideals[j]=delta                 
        #step 6                                 
        m = j-1                                 
        while m>=0: 
            #There is an error in the book here. It says to invert the j ideal instead of the m ideal.                            
            domain = ~ideals[m]*ideals[j]       
            denominator = domain.denominator().gens_reduced()[0]
            denominator*=(A[m,i]*denominator).denominator()     
            q = A[m,i]*denominator-(domain*denominator).small_residue(A[m,i]*denominator)
            q/=denominator                                                               
            A[m]-=q*A[j]                                                                 
            m-=1                                                                         
        i+=1                                                                             
        j+=1                                                                             
    return A,ideals   


#Si_reduce takes a basis for an Ok module A and a quadratic form Q and returns a basis B generated by the Si method
def Si_reduce(A,Q):                                  
    n = A.rank()                                 
    m = A[0].degree()                                                               
    K = A[0,0].parent()                  
    Ok = K.ring_of_integers()                                      
    d = K.degree()
    #intversion is the higher-dimension integer basis corresponding to A                                                 
    intversion = zero_matrix(QQ,n*d,m*d)                                                                           
    for basis in range(n*d):                                                                                       
        for entry in range(m*d):                                                                                   
            intversion[basis,entry]=(A[floor(basis/d)][floor(entry/d)]*Ok.basis()[basis%d]).list()[entry%d]
    denominator = intversion.denominator()
    intversion = intversion*denominator 
    #after LLL-reducing the integer basis we convert back to field vectors and select n linearly-independent vectors            
    intversion = qLLL(intversion,Q)
    FieldMatrix = zero_matrix(K,n*d,m)
    for basis in range(n*d):  
        for entry in range(m):                                    
            value = 0                                             
            for i in range(d):                                    
                value += intversion[basis,entry*d+i]*Ok.basis()[i]
            FieldMatrix[basis,entry]=value
    FieldMatrix = basis_sort(FieldMatrix,Q)     
    Si = findSi(FieldMatrix,A)                           
    Si = Si/denominator
    #Si can be given in terms of the basis A, and then by finding the BPC_HNF of T we transform A                                 
    T = Si*~A       
    H,ideals = bpc_hnf(T.transpose(),[Ok*1 for i in range(n)])
    #Here we have Si=TA and H=UT.transpose() which combine to give TA=H.transpose()*~U.transpose()*A=Si so B=~U.transpose*A=~H.transpose()*Si
    #Note that we end up not needing U so I do not include it in the bpc_hnf method
    B = ~H.transpose()*Si
    for i in range(n):
        ideal = ideals[i]
        x = ideal.gens_reduced()[0]
        ideals[i]=ideal/x
        B[i]/=x
        reset('x')                          
    B = basis_sort(B,Q)
    return B,ideals
