import collections,sys
f=sys.argv[1]
groups={
 'subst.apply (ScSubstitutor.apply)':['recursiveUpdate/ScSubstitutor.apply'],
 'this-walk (doUpdateThisTypeFromClass)':['doUpdateThisTypeFromClass'],
 'BaseTypes.baseType':['BaseTypes$.baseType'],
 'BaseTypes (any)':['types/BaseTypes$'],
 'canonicalizeTarget':['ThisTypeSubstitution$.canonicalizeTarget'],
 'collapseSingletonPath':['collapseSingletonPath'],
 'designatorSingletonType':['designatorSingletonType'],
 'ScProjectionType.actualImpl':['ScProjectionType.actualImpl'],
 'isMoreNarrow':['isMoreNarrow'],
 'isInheritor(Deep)':['isInheritorDeep','ScTemplateDefinitionImpl.isInheritor'],
 'ownerChainMatches':['ownerChainMatches'],
 'MixinNodes':['typedef/MixinNodes'],
 'TypeDefinitionMembers':['typedef/TypeDefinitionMembers'],
 'BaseProcessor.processType':['BaseProcessor.processType'],
 'conformance':['ScalaConformance','Conformance$'],
 'ScalaColorSchemeAnnotator':['ScalaColorSchemeAnnotator'],
}
tot=0; scala=0; incl=collections.Counter(); within=collections.Counter(); wtot=0
union=0
for line in open(f):
  st,n=line.rsplit(' ',1); n=int(n); tot+=n
  if 'org/jetbrains/plugins/scala' not in st: continue
  scala+=n
  hit=set()
  for g,pats in groups.items():
    if any(p in st for p in pats): hit.add(g)
  for g in hit: incl[g]+=n
  if any(p in st for p in ['recursiveUpdate/ScSubstitutor.apply','ThisTypeSubstitution$.canonicalizeTarget','BaseTypes$.baseType','doUpdateThisTypeFromClass']): union+=n
  if 'doUpdateThisTypeFromClass' in st:
    wtot+=n; rest=st[st.index('doUpdateThisTypeFromClass'):]
    for k in ['BaseTypes$.baseType','isMoreNarrow','isInheritor','ownerChainMatches','extractAll','mergeSameClass','supersOf','designatorSingletonType','ScSubstitutor.apply']:
      if k in rest: within[k]+=n
print(f'all samples {tot}, plugin samples {scala} ({scala/tot*100:.0f}%)')
print(f'{union/scala*100:5.1f}%  UNION apply|canonicalize|baseType|walk')
for g,v in sorted(incl.items(), key=lambda x:-x[1]): print(f'{v/scala*100:5.1f}%  {g}')
print('--- inside the this-walk (% of walk samples)')
for k,v in within.most_common(): print(f'{v/max(wtot,1)*100:5.1f}%  {k}')
