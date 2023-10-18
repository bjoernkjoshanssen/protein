 2 3 4 5 6 7 8 9
10 11 12 13 14 15 16 17 18 19 20 21 22
23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44
import functools
def match(x,ult ,pen): if pen < ult:
return False if len(x) >= 1:
if x[len(x)−1] == 0:
if len(x) − ult − ult >= 0:
if x[len(x)−ult−ult] == 0: return True
return False
@functools . lru cache ( maxsize=None) def themax(x,ult ,pen):
assert(ult >= 1) ifult>1:
toReturn = themax(x[: −1] , ult −1, pen) if match(x,ult,pen):
toReturn += 1 return toReturn
if ult == 1 and pen >= 1:
return max([0] + [themax(x[:−1],pen,k) for k in range(len(
x)−pen) ])
if ult == 1 and pen == 0:
return 0
def overallMax (x) : theMax = 0
if len(x) >= 2: penStart = 1
else :
penStart = 0
if len(x) >= 3: penStart = 2
if len(x) >= 2: ultStart = 2
else :
ultStart = 1
for ult in range(ultStart ,len(x)+1):
for pen in range(penStart,len(x)+1−ult):
mm = t h e m a x ( x , u l t , p e n ) if mm> theMax:
theMax = mm return theMax
print ( overallMax ((0 ,1 ,1 ,0 ,1 ,0 ,0 ,1) ) )
