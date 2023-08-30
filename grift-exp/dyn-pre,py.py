import pandas as pd

df = pd.read_csv('bug-dyn-pre.csv')
wdn_num = df['wdn-num']
wdn_tp = df['tp-wdn']
df_fp = df[df['wdn-num']>df['tp-wdn']]
sampled_df = df.sample(n=20)
with open('sample_fp_wdn.txt','w') as f:
    for value in sampled_df['path']:
        f.write(str(value)+'\n')

