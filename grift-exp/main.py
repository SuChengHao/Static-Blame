# This is a sample Python script.

# Press Shift+F10 to execute it or replace it with your code.
# Press Double Shift to search everywhere for classes, files, tool windows, actions, and settings.

import matplotlib.pyplot as plt
import matplotlib as mpl
import matplotlib.transforms as transforms
import pandas as pd
import numpy as np

readData = pd.read_csv("final report.csv")

validReportData = readData[readData['accepted?']]

filteredValidReportData = validReportData[
    (validReportData['mutator'] == 'arithmetic') | (validReportData['mutator'] == 'constant-swap') | (
            validReportData['mutator'] == 'position-swap')]

# cas_list = ['blackscholes', 'fft', 'matmult', 'n_body', 'quicksort', 'ray', 'sieve', 'tak']
cas_list = ['blackscholes', 'fft', 'matmult', 'n_body', 'quicksort', 'ray', 'tak']
loc_list = [139, 99, 38, 21, 47, 199, 17]
annotation_list = [128, 67, 33, 136, 44, 280, 8]
cas_data_list = [filteredValidReportData[filteredValidReportData["cas"] == i] for i in cas_list]
size_list = [s.shape for s in cas_data_list]

mutator_list = ['arithmetic', 'constant-swap', 'position-swap']


def print_latex_table_case_mutator():
    # print valid and blame situations
    # only choose one of three mutators:
    filteredValidReportData = validReportData[
        (validReportData['mutator'] == 'arithmetic') | (validReportData['mutator'] == 'constant-swap') | (
                validReportData['mutator'] == 'position-swap')]
    for c in cas_list:
        print("& ", c, end=" ")
    print("& overall", end=" ")
    print("\\\\")
    for m in mutator_list:
        print(m, end=" ")
        mut_scenarios = filteredValidReportData[filteredValidReportData['mutator'] == m]
        for c in cas_list:
            len_c, _ = (mut_scenarios[mut_scenarios["cas"] == c]).shape

            print("& ", len_c, end=" ")
        print("& ", mut_scenarios.shape[0], end=" ")
        print("\\\\")
    print("overall ", end=" ")
    for c in cas_list:
        validCaseData = filteredValidReportData[filteredValidReportData["cas"] == c]
        print("& ", validCaseData.shape[0], end=" ")
    print("\\\\")


print_latex_table_case_mutator()


def reportDataByCase(cas, cas_data, loc, nann):
    blame_data = cas_data[cas_data["blame error?"] == 'true']
    Number_Legal_Scenerios = cas_data.shape[0]
    Number_Blame_Scenerios = blame_data.shape[0]
    normalTriggedData = blame_data[blame_data["hit as normal"] == 'true']
    Number_normalHit = normalTriggedData.shape[0]
    strictTriggeredData = blame_data[blame_data["hit as strict"] == 'true']
    Number_strictHit = strictTriggeredData.shape[0]
    normalHitRate = Number_normalHit / Number_Blame_Scenerios
    strictHitRate = Number_strictHit / Number_Blame_Scenerios
    print(cas, loc, nann, Number_Legal_Scenerios, Number_Blame_Scenerios, Number_normalHit, normalHitRate,
          Number_strictHit, strictHitRate, sep=" & ", end="\\\\\n")

    # print(cas + ':')
    # blame_data = cas_data[cas_data["blame error?"] == 'true']
    # count_full_scenarios, _ = cas_data.shape
    # print("count of all scenarios generated by this mutator:", count_full_scenarios)
    #
    # count_valid_scenarios, _ = blame_data.shape
    # print("count of valid scenarios: ", count_valid_scenarios)
    #
    # mean_annotations = blame_data["anntations"].mean()
    # mean_nnor = blame_data["Normal"].mean()
    # mean_nstr = blame_data["Strict"].mean()
    # max_nnor = blame_data["Normal"].max()
    # max_nstr = blame_data["Strict"].max()
    # print("mean count of annotations: ", mean_annotations,
    #       " mean count of normal: ", mean_nnor,
    #       " mean count of strict: ", mean_nstr,
    #       " max count of normal: ", max_nnor,
    #       " max count of strict: ", max_nstr)
    #
    # normalTriggedData = blame_data[blame_data["hit as normal"] == 'true']
    # count_normal_hit, _ = normalTriggedData.shape
    # print("count of normal hit: ", count_normal_hit)
    # strictTriggeredData = blame_data[blame_data["hit as strict"] == 'true']
    # count_strict_hit, _ = strictTriggeredData.shape
    # print("count of strict hit: ", count_strict_hit)


for i in range(len(cas_list)):
    reportDataByCase(cas_list[i], cas_data_list[i], loc_list[i], annotation_list[i])

arithData = validReportData[validReportData["mutator"] == 'arithmetic']
blameArithData = arithData[arithData["blame error?"] == 'true']

condData = validReportData[validReportData["mutator"] == 'condition']
blameCondData = condData[condData["blame error?"] == 'true']

constant_swap_Data = validReportData[validReportData["mutator"] == 'constant-swap']
blame_constant_swap_Data = constant_swap_Data[constant_swap_Data["blame error?"] == 'true']

pos_swap_Data = validReportData[validReportData["mutator"] == 'position-swap']
blame_pos_swap_Data = pos_swap_Data[pos_swap_Data["blame error?"] == 'true']


def reportRelatedData(mutator, mutator_data):
    print(mutator + ':')
    blame_data = mutator_data[mutator_data["blame error?"] == 'true']
    count_full_scenarios, _ = mutator_data.shape
    print("count of all scenarios generated by this mutator:", count_full_scenarios)

    count_valid_scenarios, _ = blame_data.shape
    print("count of valid scenarios: ", count_valid_scenarios)

    mean_annotations = blame_data["anntations"].mean()
    mean_nnor = blame_data["Normal"].mean()
    mean_nstr = blame_data["Strict"].mean()
    max_nnor = blame_data["Normal"].max()
    max_nstr = blame_data["Strict"].max()
    print("mean count of annotations: ", mean_annotations,
          " mean count of normal: ", mean_nnor,
          " mean count of strict: ", mean_nstr,
          " max count of normal: ", max_nnor,
          " max count of strict: ", max_nstr)

    normalTriggedData = blame_data[blame_data["hit as normal"] == 'true']
    count_normal_hit, _ = normalTriggedData.shape
    print("count of normal hit: ", count_normal_hit)
    strictTriggeredData = blame_data[blame_data["hit as strict"] == 'true']
    count_strict_hit, _ = strictTriggeredData.shape
    print("count of strict hit: ", count_strict_hit)

def reportPrecision(filteredValidReportData):

    #calculating the precision for normal potential error
    positiveData = filteredValidReportData[filteredValidReportData['Normal'] > 0]
    countPositive, _ = positiveData.shape
    print("count of all normal potential error positive", countPositive)

    blame_data = positiveData[positiveData["blame error?"] == 'true']
    num_blame, _ = blame_data.shape
    print("count of blames ", num_blame)
    normalTriggedData = blame_data[blame_data["hit as normal"] == 'true']
    count_normal_hit, _ = normalTriggedData.shape
    print("count of all normal hits ", count_normal_hit)
    print("normal precision: ", count_normal_hit/countPositive)

    strictPositiveData = filteredValidReportData[filteredValidReportData['Strict'] > 0]
    countPositive, _ = strictPositiveData.shape
    print("count of all strict potential error positive", countPositive)
    blame_data = strictPositiveData[strictPositiveData["blame error?"] == 'true']
    num_blame, _ = blame_data.shape
    print("count of blames", num_blame)
    strictTriggeredData = blame_data[blame_data["hit as strict"] == 'true']
    count_strict_hit, _ = strictTriggeredData.shape
    print("count of all strict hits", count_strict_hit)
    print("strict precision: ", count_strict_hit/countPositive)


reportPrecision(filteredValidReportData)
reportRelatedData('arithmetic', arithData)
reportRelatedData('condition', condData)
reportRelatedData('constant-swap', constant_swap_Data)
reportRelatedData('position-swap', pos_swap_Data)

#first version
#configuration_data = pd.read_csv("configuration test.csv")
#second version, 20230824
configuration_data = pd.read_csv("bug_dectector_new_size_lat_test/lattice_test.csv")
percentage_line = configuration_data['percentage'].tolist()
dum_constraint_line = configuration_data['count of dummy constraints'].tolist()
n_dum_constraint_line = configuration_data['count of not dummy constraints'].tolist()
config_runtime_line = (configuration_data['time'] / 1000).tolist()

n_constraint_line = (configuration_data['count of dummy constraints'] + configuration_data[
    'count of not dummy constraints']).tolist()

fig,(ax1,ax2,ax3) = plt.subplots(1,3,figsize=(10,5),layout='constrained')
l1, = ax1.plot(percentage_line, dum_constraint_line,'b+')
l2, = ax2.plot(percentage_line, n_dum_constraint_line,"b+")
l3, = ax3.plot(percentage_line, n_constraint_line,"b+")
ax1.set_title("All type flows")
ax2.set_title("non-dummy flows")
ax3.set_title("dummy flows")
ax1.set_ylabel("Number of type flows")
ax2.set_ylabel("Number of type flows")
ax3.set_ylabel("Number of type flows")
ax1.set_xlabel("How much is typed(%)")
ax2.set_xlabel("How much is typed(%)")
ax2.set_ylim(ax1.get_ylim())
ax3.set_xlabel("How much is typed(%)")
plt.show()

fig,(ax1,ax2) = plt.subplots(1,2,figsize=(10,5),layout='constrained')
l1, = ax1.plot(percentage_line, dum_constraint_line,'b+')
scatter_line = [100*dum_constraint_line[i] / n_constraint_line[i] for i in range(len(percentage_line))]
sc = ax2.scatter([100*dum_constraint_line[i]/n_constraint_line[i] for i in range(len(n_dum_constraint_line))],n_constraint_line, c = percentage_line, vmin=0,vmax=100, alpha=0.7)

#cmap = mpl.colormaps['viridis']
#norm = mpl.colors.Normalize(vmin=0, vmax=100)

plt.colorbar(sc,
              location = 'right', label='proportion of type annotation') #fraction=0.05, pad=0.04,shrink=0.1


ax1.set_title("Toal type flows vs. annotation proportion")
ax2.set_title("Total type flows vs. dummy proportion")
ax1.set_ylabel("Number of type flows")
ax2.set_ylabel("Number of type flows")
ax1.set_xlabel("Type annotation proportion(%)")
ax2.set_xlabel("Dummy type flow proprotion (%)")
#ax2.set_ylim(ax1.get_ylim())
plt.show()

def drawPieMarker(xs, ys, ratios, sizes, colors):
    assert sum(ratios) <= 1, 'sum of ratios needs to be < 1'

    markers = []
    previous = 0
    # calculate the points of the pie pieces
    for color, ratio in zip(colors, ratios):
        this = 2 * np.pi * ratio + previous
        x  = [0] + np.cos(np.linspace(previous, this, 10)).tolist() + [0]
        y  = [0] + np.sin(np.linspace(previous, this, 10)).tolist() + [0]
        xy = np.column_stack([x, y])
        previous = this
        markers.append({'marker':xy, 's':np.abs(xy).max()**2*np.array(sizes), 'facecolor':color})

    # scatter each of the pie pieces to create pies
    for marker in markers:
        ax.scatter(xs, ys, **marker)

def draw_pie(dist,
             xpos,
             ypos,
             size,
             colors,
             ax=None):
    if ax is None:
        fig, ax = plt.subplots(figsize=(10,8))

    # for incremental pie slices
    cumsum = np.cumsum(dist)
    cumsum = cumsum/ cumsum[-1]
    pie = [0] + cumsum.tolist()

    for r1, r2, color in zip(pie[:-1], pie[1:],colors):
        angles = np.linspace(2 * np.pi * r1, 2 * np.pi * r2)
        x = [0] + np.cos(angles).tolist()
        y = [0] + np.sin(angles).tolist()

        xy = np.column_stack([x, y])

        ax.scatter([xpos], [ypos], marker=xy, s=size, facecolor=color)

    return ax
#create a scatter pie chart
#fig,ax = plt.subplots(figsize=(10,6))
#scatter_line = [n_dum_constraint_line[i] / n_constraint_line[i] for i in range(len(percentage_line))]
#colors = plt.cm.Set3(np.linspace(0,1,len(percentage_line)))
#indices = np.random.choice(range(len(percentage_line)),size=278, replace= None)

#for i in range(len(n_dum_constraint_line)):
#for i in indices:
    #drawPieMarker(percentage_line[i],n_constraint_line[i],[n_dum_constraint_line[i]/n_constraint_line[i],dum_constraint_line[i]/n_constraint_line[i]],[10,10],['yellow','blue'])
#    draw_pie([n_dum_constraint_line[i],dum_constraint_line[i]],percentage_line[i],n_constraint_line[i],100,['#EEBF6D','#834026'],ax)
#scatter = ax.scatter([dum_constraint_line[i]/n_constraint_line[i] for i in range(len(n_dum_constraint_line))],n_constraint_line, c = scatter_line, vmin=0,vmax=1, alpha=0.7)
# for i in range(len(percentage_line)):
#      wedges, _ = ax.pie([n_dum_constraint_line[i], dum_constraint_line[i]],radius=0.2,colors=colors)
#      plt.setp(wedges, width=0.1)
# #
# #     # Adjust the position of the pie chart markers
#      trans = transforms.blended_transform_factory(ax.transData, ax.transAxes)
#      for j, wedge in enumerate(wedges):
#          trans_offset = transforms.offset_copy(
#              wedge.get_transform(), x=percentage_line[i], y=n_constraint_line[i], units='dots')
#          wedge.set_transform(trans_offset)
# #     #    # Add labels to the pie chart markers
# #         #ax.text(x[i], y[i], labels[j], ha='center', va='center', fontsize=8)
#ax.set_title('All type flows of each scenario')
#ax.set_xlabel('How much is typed(%)')
#ax.set_ylabel('Number of type flows')
#plt.show()


fig, ax = plt.subplots()
line1, = ax.plot(percentage_line,config_runtime_line, 'gx',label='run time')
ax.set_xlabel("How much is typed(%)")
ax.set_ylabel("Run time(s)")
#ax.set_title("Static Blame Configuration Test")
ax.set_title("SLOG Lattice Test")
plt.show()
# fig = plt.figure()
# plt.subplot(1, 3, 1)
# plt.scatter(percentage_line, dum_constraint_line)
# plt.title("dummy type flows")
# plt.xlabel("percentage(%)")
# plt.ylabel("number of type flows")
#
# plt.subplot(1, 3, 2)
# plt.scatter(percentage_line, n_dum_constraint_line)
# plt.title("non-dummy type flows")
# plt.xlabel("percentage(%)")
# plt.ylabel("number of type flows")
#
# plt.subplot(1, 3, 3)
# plt.scatter(percentage_line, n_constraint_line)
# plt.title("type flows")
# plt.xlabel("percentage(%)")
# plt.ylabel("number of type flows")
# plt.show()

#size_data = pd.read_csv("size test.csv")
size_data = pd.read_csv("bug_dectector_new_size_lat_test/size_config.csv")
size_loc = size_data['loc'].tolist()
size_dum_constraint_line = size_data['count of dummy constraints'].tolist()
size_time = (size_data['time']/1000).tolist()
def cal_increment(l):
    ret = []
    for i in reversed(range(len(l))):
        if i == 0: ret.append(0)
        else:
            ret.append(l[i] - l[i - 1])
    ret.reverse()
    return ret
size_increment = []
for i in reversed(range(len(size_loc))):
    if i == 0: size_increment.append(0)
    else:
        size_increment.append(size_dum_constraint_line[i] - size_dum_constraint_line[i - 1])
size_increment.reverse()

import matplotlib.lines as mlines

# fig, ax = plt.subplots()
# #line1 = mlines.Line2D(size_loc,size_dum_constraint_line,color='green',linestyle='--',label='number of type flows')
# line1, = ax.plot(size_loc, size_dum_constraint_line,'b--',label='number of type flows',marker='o')
# incrementline, = ax.plot(size_loc, size_increment,'c--',label='number of increment',marker='o')
# ax.legend(handles=[line1,incrementline])
# ax.set_xlabel('LOC')
# ax.set_ylabel('Number of type flows')
# ax.set_title('Static Blame Size Test')
# plt.show()

fig, ax  = plt.subplots()
line1, = ax.plot(size_loc,size_time,                'b--',marker='o',label='run time')
line2, = ax.plot(size_loc,cal_increment(size_time), 'c--', marker='o',label='increment of run time')
ax.legend(handles=[line1,line2])
ax.set_xlabel('LOC')
ax.set_ylabel('Run time(s)')
#ax.set_title('Static Blame Size Test')
ax.set_title('SLOG Size Test')
plt.show()


#
# fig = plt.figure
# plt.plot(size_loc, size_dum_constraint_line,'g--',size_loc,size_dum_constraint_line,'bo')
# plt.plot(size_loc, size_increment,'y--', size_loc, size_increment, 'co')
# plt.show()
#
# cons_list = filteredValidReportData['constraints'].tolist()
# runtime_list = filteredValidReportData["analyse time"].tolist()
# plt.plot(cons_list, runtime_list, 'gx')
# plt.title("Static Blame on Blame Scenarios")
# plt.xlabel("number of generated type flows")
# plt.ylabel("Static Blame run time (milisecond)")
# plt.show()



# dataloc = readData.iloc[:, 1].tolist()
# datanum = readData.iloc[:, 4].tolist()
#
# dataNormal = readData.iloc[:, 7].tolist()
# dataStrict = readData.iloc[:, 8].tolist()
# dataWrong = readData.iloc[:, 9].tolist()
#
# dataBlame = readData.iloc[:, 2].tolist()
# dataHit = readData.iloc[:, 5].tolist()
# dataSHit = readData.iloc[:, 6].tolist()
#
# sumBlame = sum(1 for i in dataBlame if i == "#t")
# sumHit = sum(1 for i in dataHit if i == "#t")
# sumSHit = sum(1 for i in dataSHit if i == "#t")
# sumofall = len(dataBlame)
#
# print(
#     f"in {sumofall} files, {sumBlame} triggers Blame, where {sumHit} is normal potential, but {sumSHit} is strict potential")
# print(sumBlame, sumHit, sumSHit, sumofall)

# plt.scatter(dataloc,dataWrong)
# plt.title("Wrong Dyn")
# plt.xlabel("loc")
# plt.ylabel("num of Wrong Dyn")
# plt.show()
