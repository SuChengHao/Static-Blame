import matplotlib.pyplot as plt
import pandas as pd
from collections import Counter

'''
with open('data-collection.csv','r') as file:
    lines = file.readlines()

with open('new-data-collection.csv','w') as file:
    for line in lines:
        if not line.startswith('[Case]'):
            file.write(line)
'''


dynamized_errors = ['/exp/blackscholes/position-swap/mutant69',
                    "/exp/matmult/arithmetic/mutant11/",
                    "/exp/matmult/arithmetic/mutant12/",
                    "/exp/matmult/arithmetic/mutant13/",
                    "/exp/matmult/arithmetic/mutant14/"]


#df = pd.read_csv('new-data-collection.csv')
#df = pd.read_csv('up-bug-detection-data.csv')
pdf = pd.read_csv('up-normal-pos-bug-detection-data.csv')
#remove all files that cannot be dynamized
edf = pdf[~pdf['path'].str.startswith(tuple(dynamized_errors))]

#now we remove all condition mutations from the table
df = edf[~edf['path'].str.contains('condition')]

listofpaths = df['path'].tolist()
components = [(path.split('/')[2],path.split('/')[3] )for path in listofpaths]
counts = Counter(components)

for i, ((element1, element2), count) in enumerate(counts.items()):
    if i%3 == 0:
        print('\n', element1, '&', end=" ")
    print(count, '&', end=" ")


npe_num = df['npe-num']
npe_tp = df['tp-npe']
spe_num = df['spe-num']
spe_tp = df['tp-spe']
wdn_num = df['wdn-num']
wdn_tp = df['tp-wdn']







sum_npe_num = npe_num.sum()
mean_npe_num = npe_num.mean()
sum_npe_tp = npe_tp.sum()

sum_spe_num = spe_num.sum()
mean_spe_num = spe_num.mean()
sum_spe_tp = spe_tp.sum()

sum_wdn_num = wdn_num.sum()
mean_wdn_num = wdn_num.mean()
sum_wdn_tp = wdn_tp.sum()

print(f"Number of all files:{len(df)}")
print(f"All NPE: {sum_npe_num}, true positive: {sum_npe_tp}/{sum_npe_num} = {sum_npe_tp/sum_npe_num:.2%}")

print(f"All SPE: {sum_spe_num}, true positive: {sum_spe_tp}/{sum_spe_num} = {sum_spe_tp/sum_spe_num:.2%}")
print(f"All WDN: {sum_wdn_num}, true positive: {sum_wdn_tp}/{sum_wdn_num} = {sum_wdn_tp/sum_wdn_num:.2%}")
print(f"mean npe:{mean_npe_num}, mean SPE:{mean_spe_num}, mean WDN: {mean_wdn_num}")
print(f"possible recall npe:{(df['tp-npe']>0).sum()/len(df):.2%} spe: {(df['tp-spe']>0).sum()/len(df):.2%}, wdn:{(df['tp-wdn']>0).sum()/len(df):.2%}")


print(f'NPE: number of true positive files,{(df["tp-npe"]>0).sum()}')
print(f'SPE: number of true positive files,{(df["tp-spe"]>0).sum()}')
print(f'WDN: number of true positive files,{(df["tp-wdn"]>0).sum()}')

print(f'NPE: number of false negative files, {len(df) - (df["tp-npe"]>0).sum()}')
print(f'SPE: number of false positives:{sum_spe_num - sum_spe_tp}, num of false negative files:{len(df) - (df["tp-spe"]>0).sum()}')
print(f'WDN: number of false positives:{sum_wdn_num - sum_wdn_tp}, number of false negative files:{len(df) - (df["tp-wdn"]>0).sum()}')



print(f'SPE: number of false positive files:{len(df[df["spe-num"] > df["tp-spe"]])}')
print(f'WDN: number of false positive files:{len(df[df["wdn-num"] > df["tp-wdn"]])}')
# sample all with fp
df_wdn_nums=df[df['wdn-num']>0]
df_fps = df_wdn_nums[df_wdn_nums['wdn-num']>df_wdn_nums['tp-wdn']]



#df_fps=df_wdn_nums[df_wdn_nums['wdn-fp']>0]
#df_fps.to_csv('wdn-fps.csv',index=False)