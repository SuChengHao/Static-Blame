
import pandas as pd

df = pd.read_csv('up-bug-detection-data.csv')
#df = pd.read_csv('new-data-collection.csv')
spe_num = df['spe-num']
spe_tp = df['tp-spe']
wdn_num = df['wdn-num']
wdn_tp = df['tp-wdn']

df_spe_nums=df[df['spe-num']>0]
df_fps = df_spe_nums[df_spe_nums['spe-num']>df_spe_nums['tp-spe']]

#how many rows?
num_rows = df_fps.shape[0]
#3065, sample 306
print(num_rows)
sampled = df_fps.sample(n=200)
#sampled.to_csv('spe-fps-v2.csv',index=False)