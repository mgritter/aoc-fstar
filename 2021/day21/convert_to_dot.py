import sys

max_days = 5
player = 1

keys = set()

def key( s1, p1, s2, p2 ):
 return f"n_{s1}_{p1}_{s2}_{p2}"

def label( s1, p1, s2, p2 ):
 return f"{s1}@{p1}\\n{s2}@{p2}"

print( "digraph {" )
print( "  node [color=none; shape=plaintext];" )
print( "   node [ fontsize=3 ];" )
print( "   edge [ arrowsize=0.1 ];" )
for line in sys.stdin:
    if line == "next time step!\n":
        max_days -= 1
        player = (1 if player == 2 else 2)
        if max_days == 0:
           break
        continue

    tok = line.split( ' ' )
    score1 = int( tok[4] )
    pos1 = int( tok[6][:-1] )
    score2 = int( tok[9] )
    pos2 = int( tok[11] )

    k = key( score1, pos1, score2, pos2 )
    if k not in keys:
        l = label(score1, pos1, score2, pos2)
        print( f"{k} [label=\"{l}\"];" )
        keys.add( k )

    if max_days > 1:     
        if player == 1 and score1 < 21 and score2 < 21:
            successors = []
            for d3 in [3,4,5,6,7,8,9]:
                p = ( pos1 + d3 ) % 10
                if p == 0:
                    p = 10
                s = score1 + p
                successors.append( key( s, p, score2, pos2 ) )
            for s in successors:
                print( f"{k} -> {s};" )
        if player == 2 and score1 < 21 and score2 < 21:
            successors = []
            for d3 in [3,4,5,6,7,8,9]:
                p = ( pos2 + d3 ) % 10
                if p == 0:
                    p = 10
                s = score2 + p
                successors.append( key( score1, pos1, s, p ) )
            for s in successors:
                print( f"{k} -> {s};" )

print( "}" )

                
    
