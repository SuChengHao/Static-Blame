import pandas
import pandas as pd
from collections import Counter
dynamized_errors = ['/exp/blackscholes/position-swap/mutant69',
                    "/exp/matmult/arithmetic/mutant11/",
                    "/exp/matmult/arithmetic/mutant12/",
                    "/exp/matmult/arithmetic/mutant13/",
                    "/exp/matmult/arithmetic/mutant14/"]


def df_remove_invalid_lines(df: pd.DataFrame, path_index='path'):
    edf = df[~df[path_index].str.startswith(tuple(dynamized_errors))]
    return edf[~edf[path_index].str.contains('condition')]


def parse_reason(reasons:str):
    #first, split by |
    reason_list = reasons.split('|')
    #then, for each element, parse a
    reasons = []
    for tok in reason_list:
        toks = tok.split('*')
        if (len(toks) == 1):
            reasons.append(tok)
        else:
            repeat = int(toks[1])
            reasons = reasons + ([toks[0]]*repeat)
    return reasons

parse_reason('grift-impl|elsewhere*10')
# firstly, we analyse the false positives of wdt

wdt_fps = pd.read_csv('annotation/wdn-fps-transformed-work.csv')

def verify_fps_reasons(fps_dataframe_file):
    fps_dataframe = pd.read_csv(fps_dataframe_file)
    for index, row in fps_dataframe.iterrows():
        rowreasons = parse_reason(row['reasons'])
        nfps = row['number-of-false-positive']
        if not (nfps == len(rowreasons)):
            raise Exception(f'the row{row} is not well-annotated')
        #emptycounter += Counter(rowreasons)

valid_wdt_fps = df_remove_invalid_lines(wdt_fps,path_index='file-path')


emptycounter = Counter()
#now, analyse each row
#verify_fps_reasons(valid_wdt_fps)
print(emptycounter)


def print_counter_percentage(counter):
    total = sum(counter.values())
    for key, value in counter.items():
        print(f"{key}: {value/total:.2%}")
def printFPS(file):
    emptycounter = Counter()
    df = pd.read_csv(file)
    for index, row in df.iterrows():
        rowreasons = parse_reason(row['reasons'])
        nfps = row['number-of-false-positive']
        if not (nfps == len(rowreasons)):
            raise Exception(f'the row{row} is not well-annotated')
        emptycounter += Counter(rowreasons)
    print(emptycounter)
    print_counter_percentage(emptycounter)

def printFNS(file):
    emptycounter = Counter()
    df = pd.read_csv(file)
    for index, row in df.iterrows():
        reason = [row['reason']]
        emptycounter += Counter(reason)
    print(emptycounter)
    print_counter_percentage(emptycounter)


updated_frame = pandas.read_csv('up-normal-pos-bug-detection-data.csv')
spe_fps = pd.read_csv('annotation/spe-fps-v2-transformed-work.csv')

def spe_fps_ana():
    # then, we are ready to process the false positives of spe
    # before that, since the match process has been updated, we need to fresh it.
    spe_fps = pd.read_csv('annotation/spe-fps-v2-transformed-work.csv')
    # first, filter it
    spe_filtered = df_remove_invalid_lines(spe_fps, path_index='file-path')

    list_of_fps_need_to_update = []
    # compare it with updated files, and print all lines with different false positive numbers.
    for index, row in spe_filtered.iterrows():
        path = row['file-path']
        updated_rows = updated_frame.loc[updated_frame['path'] == path]
        updated_row = updated_rows.iloc[0]
        if not ((updated_row['spe-num'] - updated_row['tp-spe']) == row['number-of-false-positive']):
            list_of_fps_need_to_update.append(path)

    # re-sample, first clear all rows in old spe
    sample_one = updated_frame[~updated_frame['path'].isin(spe_filtered['file-path'])]
    # then, remove all rows without false positives
    # df_spe_nums=df[df['spe-num']>0]
    # df_fps = df_spe_nums[df_spe_nums['spe-num']>df_spe_nums['tp-spe']]
    sample_one = sample_one[sample_one['spe-num'] > 0]
    sample_one = sample_one[sample_one['spe-num'] > sample_one['tp-spe']]
    # sample length of list_of_fps
    sampled = sample_one.sample(n=len(list_of_fps_need_to_update))

    # then remove the list_of_fps from
    healthy_spe = spe_filtered[~spe_filtered['file-path'].isin(list_of_fps_need_to_update)]

    mergeres = pd.merge(updated_frame, healthy_spe, left_on='path', right_on='file-path')
    mergeres = mergeres[mergeres.columns.intersection(updated_frame.columns)]
    # mergeres = pd.merge(mergeres,sampled,on='path')
    # then extract all of them, write mergeres into files

    mergeres = pd.concat([mergeres, sampled])
    mergeres.to_csv('annotation/spe_fps_want_to_transformed.csv', index=False)

    analyse_transformed = pd.read_csv('annotation/spe_fps_analyse_transformed.csv')
    for index, row in analyse_transformed.iterrows():
        tmp_rows = spe_fps[spe_fps['file-path'] == row['file-path']]
        if not (tmp_rows.empty):
            analyse_transformed.loc[index, 'reasons'] = tmp_rows.iloc[0]['reasons']

    analyse_transformed.to_csv('annotation/to_annote.csv', index=False)
    spe_fns = pd.read_csv('annotation/spe-fns-v2-transformed-work.csv')
    # clear all invalid rows, see if there is a need to resample.

    spe_valid_fns = df_remove_invalid_lines(spe_fns, path_index='file-path')
    # remove from updated_frame with all rows occurs in spe_valid_fns
    sample_one = updated_frame[~updated_frame['path'].isin(spe_valid_fns['file-path'])]
    sample_one = sample_one[sample_one['tp-spe'] == 0]

    sample1 = sample_one.sample(n=(200 - spe_valid_fns.shape[0]))
    mergeres = pd.merge(updated_frame, spe_valid_fns, left_on='path', right_on='file-path')
    mergeres = mergeres[mergeres.columns.intersection(updated_frame.columns)]
    mergeres = pd.concat([mergeres, sample1])
    # mergeres.to_csv('annotation/spe_fns_want_to_transformed.csv', index=False)

    analyse_transformed = pd.read_csv('annotation/spe_fns_analyse_transformed.csv')
    for index, row in analyse_transformed.iterrows():
        tmp_rows = spe_valid_fns[spe_valid_fns['file-path'] == row['file-path']]
        if not (tmp_rows.empty):
            analyse_transformed.loc[index, 'reason'] = tmp_rows.iloc[0]['reason']

    analyse_transformed.to_csv('annotation/to_annote.csv', index=False)

# 2023/07/13
# Today's destination: finish experiment
# statistic all false postives,

def resample_spe_fns(old_finish_file, all_scenario_file, sample_size, new_filename):
    old_finish_spe_fns = pd.read_csv(old_finish_file)
    all_df = pd.read_csv(all_scenario_file)
    all_df = df_remove_invalid_lines(all_df,path_index='path')
    #only reserve false positives
    all_df = all_df[all_df['tp-spe'] == 0]
    #remove all the old rows from the all_df
    filtered = all_df[all_df['path'].isin(old_finish_spe_fns['file-path'])]
    print(f'filtered {len(filtered)} files')
    all_df = all_df[~all_df['path'].isin(old_finish_spe_fns['file-path'])]
    #then resample
    old_size = len(filtered)
    print(f'old size is {old_size}, resample {sample_size - old_size} files')
    sampled = all_df.sample(sample_size - old_size)
    meg = pd.concat([filtered, sampled])
    print(f'resampled {len(meg)} files')
    meg.to_csv(new_filename, index=False)

def resample_wdt_fns(old_finish_file, all_scenario_file, sample_size, new_filename):
    old_finish_wdt_fns = pd.read_csv(old_finish_file)
    all_df = pd.read_csv(all_scenario_file)
    all_df = df_remove_invalid_lines(all_df, path_index='path')
    #only reserve false positives
    all_df = all_df[all_df['tp-wdn'] == 0]
    #remove all the old rows from the all_df
    filtered = all_df[all_df['path'].isin(old_finish_wdt_fns['file-path'])]
    print(f'filtered {len(filtered)} files')
    all_df = all_df[~all_df['path'].isin(old_finish_wdt_fns['file-path'])]
    #then resample
    old_size = len(filtered)
    print(f'old size is {old_size}, resample {sample_size - old_size} files')
    sampled = all_df.sample(sample_size - old_size)
    meg = pd.concat([filtered, sampled])
    print(f'resampled {len(meg)} files')
    meg.to_csv(new_filename, index=False)

#resample_spe_fns('annotation/spe-fns-finished-work.csv', 'up-normal-pos-bug-detection-data.csv', 371, 'second_annotation/spe_fns_waiting_transformed.csv')
#resample_wdt_fns('annotation/wdn-fns-transformed-work.csv', 'up-normal-pos-bug-detection-data.csv',372,'second_annotation/wdt_fns_waiting_transformed.csv')

#moreover, transform all spe fpses
def extract_spe_fps(all_scenario_file, new_file):
    all_df = pd.read_csv(all_scenario_file)
    all_df = df_remove_invalid_lines(all_df, path_index='path')
    print(f'length of all scenarios: {len(all_df)}')
    # find all rows such that column tp-spe is 0 but spe-num is not zero
    all_df = all_df[all_df['spe-num']>all_df['tp-spe']]
    #all_df = all_df[all_df['tp-spe']==0]
    print(f'the length of all fps:{len(all_df)}')
    all_df.to_csv(new_file,index=False)
#extract_spe_fps('up-normal-pos-bug-detection-data.csv','second_annotation/spe_wdt_waiting_transformed.csv')

#then, read the new samplings, and use old results to fill
def refill_fns(new_fns_file,old_fns_file,fresh_file):
    new_fns_df = pd.read_csv(new_fns_file)
    old_fns_df = pd.read_csv(old_fns_file)
    if not 'reason' in new_fns_df.columns:
        new_fns_df['reason'] = ""
    for index, row in new_fns_df.iterrows():
        tmp_rows = old_fns_df[old_fns_df['file-path'] == row['file-path']]
        if not (tmp_rows.empty):
            new_fns_df.loc[index, 'reason'] = tmp_rows.iloc[0]['reason']
    new_fns_df.to_csv(fresh_file,index=False)

def refill_fps(new_fps_file,old_fps_file,fresh_file):
    new_fps_df = pd.read_csv(new_fps_file)
    old_fps_df = pd.read_csv(old_fps_file)
    if not 'reasons' in new_fps_df:
        new_fps_df['reasons']=""
    for index,row in new_fps_df.iterrows():
        tmp_rows = old_fps_df[old_fps_df['file-path'] == row['file-path']]
        if not (tmp_rows.empty):
            new_fps_df.loc[index, 'reasons'] = tmp_rows.iloc[0]['reasons']
    new_fps_df.to_csv(fresh_file,index=False)

#refill_fps('second_annotation/spe_fps_after_first_transformation.csv','annotation/spe-fps-finished-work.csv','second_annotation/spe_fps_work.csv')
#refill_fns('second_annotation/spe_fns_after_first_transformation.csv', 'annotation/spe-fns-finished-work.csv', 'second_annotation/spe_fns_work.csv')
#refill_fns('second_annotation/wdt_fns_after_first_transformation.csv', 'annotation/wdn-fns-transformed-work.csv', 'second_annotation/wdt_fns_work.csv')

# The following is the first annotation
#printFPS('annotation/wdn-fps-transformed-work.csv')
#printFPS('annotation/spe-fps-finished-work.csv')
#printFNS('annotation/wdn-fns-transformed-work.csv')
#printFNS('annotation/spe-fns-finished-work.csv')

#The following is the second annotation (with calculated sample size)
verify_fps_reasons('annotation/wdn-fps-transformed-work.csv')
verify_fps_reasons('second_annotation/spe_fps_work.csv')
printFPS('annotation/wdn-fps-transformed-work.csv') # the wdt has no need to update
printFPS('second_annotation/spe_fps_work.csv')
printFNS('second_annotation/wdt_fns_work.csv')
printFNS('second_annotation/spe_fns_work.csv')

old_npe_recall = 0.36
old_spe_recall = 0.35
old_wdt_recall = 0.34

def renew_recall(old_recall, remove_percentage):
    return old_recall/( (1-remove_percentage) * (1-old_recall) + old_recall)

print(f'estimated npe recall: {renew_recall(old_npe_recall, 0.9488)}')
print(f'estimated spe recall: {renew_recall(old_spe_recall, 0.9488)}')
print(f'estimated wdt recall: {renew_recall(old_wdt_recall, 0.9274)}')