#extract fn-spe, fn-wdt
import pandas as pd

df = pd.read_csv('up-bug-detection-data.csv')
#df = pd.read_csv('new-data-collection.csv')
spe_num = df['spe-num']
spe_tp = df['tp-spe']
wdn_num = df['wdn-num']
wdn_tp = df['tp-wdn']

spe_fn = df[df['tp-spe']==0]
wdn_fn = df[df['tp-wdn']==0]

spe_fn.sample(n=200).to_csv('spe-fns-v2.csv',index=False)
#wdn_fn.sample(n=200).to_csv('wdn-fns.csv',index=False)
