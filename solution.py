
# coding: utf-8

# In[148]:


# ! export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:~/workspace/z3-4.7.1-x64-debian-8.10/bin
# ! export PYTHONPATH=~/workspace/z3-4.7.1-x64-debian-8.10/bin/python


# In[149]:


# Starting time
import time
start_time_of_program = time.time()


# In[150]:


# Importing libraries
from z3 import *
from itertools import permutations 
import itertools


# In[151]:


# Importing input file
import json
with open('newinp1.json') as f:
    input_dict = json.load(f)


# In[152]:


# Viewing input dictionary
import pprint
pprint.pprint(input_dict)


# In[153]:


# Type to Room Dictionary
type_to_room_dict = {}
for x in input_dict['Room Types']:
    type_to_room_dict[x] = []
for x in input_dict['Classrooms']:
    type_to_room_dict[x[1]].append(x[0])
type_to_room_dict


# In[154]:


# List of room and dictionary from room to its index
room_list = []
for key,value in type_to_room_dict.items():
    room_list.extend(value)
print(room_list)
room_to_index = {x:y for y,x in enumerate(room_list)}
print(room_to_index)


# In[155]:


# Days and periods
day_list_tmp = []
for j in range(5):
    for x in input_dict["Institute time"]:
        lower_bound = x[0]
        upper_bound = x[1]
        day_list_tmp.append(int((upper_bound -lower_bound)/.5))
day_dict = {}
for i in range(len(day_list_tmp)):
    day_dict[i+1] = list(range(1,day_list_tmp[i] + 1))
day_list = list(range(1,1+len(day_list_tmp)))
def periods(d):
    return day_dict[d]
print(day_list)
pprint.pprint(day_dict)


# In[156]:


# faculty list
tmp_list = []
for x in input_dict["Courses"]:
    for y in x[3]:
        tmp_list.append(y)
faculty_list = list(set(tmp_list))
faculty_to_index = {x:y for y,x in enumerate(faculty_list)}

print(faculty_list)
print(faculty_to_index)


# In[157]:


# batch list
tmp_list = []
for x in input_dict["Courses"]:
    tmp_list.append(x[4])
batch_list = list(set(tmp_list))
batch_to_index = {x:y for y,x in enumerate(batch_list)}
print(batch_list)


# In[158]:


# Course list
course_list = input_dict["Courses"]
print(course_list)


# In[159]:


# Here we are taking only first faculty in the list and we will write the codition on other faculties of the course later

tsgn = []
for s in range(len(course_list)):
    # Getting number of lecture slots
    n = len(course_list[s][2])
    faculty_name_tmp = course_list[s][3][0]
    g = course_list[s][4]
    t = faculty_to_index[faculty_name_tmp]
    for ni in range(1,n+1):
        tsgn.append((t,s,g,ni))
print(tsgn)


# In[160]:


len(course_list[0][2])


# In[161]:


# This function takes a tuple of (t,s,g,n) and gives n * .5 , where 'n' hours is the duration of class associated with this tsgn

def duration(x_tsgn):
    this_course = course_list[x_tsgn[1]]
    this_lecture_list = this_course[2]
    this_lecture_length = this_lecture_list[x_tsgn[3]-1]
    return int(this_lecture_length / .5)


# In[162]:


print(duration((2, 0, 2, 1)))


# In[163]:


# This function will take index of a faculty and return a list containing indices of courses which are being taught
# by this particular professor

def lessons_t(t):
    result = []
    for x in tsgn:
        if (x[0] == t):
            result.append(x)
    return result


# In[164]:


print(lessons_t(1))


# In[165]:


# This function will take a batch and return a list containing indices of courses which are being taught
# to this particular batch

def lessons_g(g):
    result = []
    for x in tsgn:
        if (x[2] == g):
            result.append(x)
    return result


# In[166]:


print(lessons_g(2))


# In[167]:


# Some short-hands :-
# VX.Y - Defining variables of set X.Y
# CX.Y - Defining constraints of set X.Y


# In[168]:


pd = dict() # Proposition Dictionary
# V1.1
for x in tsgn:
    for d in day_list:
        for p in range(min(periods(d)), 1 + max(periods(d)) - duration(x) + 1):
            var_name = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)
            pd[var_name] = Bool(var_name)


# In[169]:


# V1.2
for x in tsgn:
    for d in day_list:
        for p in range(min(periods(d)), 1 + max(periods(d))):
            var_name = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)
            pd[var_name] = Bool(var_name)


# In[170]:


# C1.1
constraint_1_1 = True
for x in tsgn:
    for d in day_list:
        for p1 in range(min(periods(d)), 1 + max(periods(d)) - duration(x) + 1): 
            var_name1 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p1)
            for p2 in range(p1,1 + p1 + duration(x) - 1):
                var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p2)
                constraint_1_1 = And(constraint_1_1,Implies(pd[var_name1], pd[var_name2]))


# In[171]:


# C1.2
constraint_1_2 = True
tmp_true = True
tmp_false = False
for x in tsgn:
    for d in day_list:
        for p2 in range(min(periods(d)), 1 + max(periods(d))): 
            tmp = copy.deepcopy(tmp_false)
            var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p2)
            for p1 in range(max(p2 - duration(x) + 1, min(periods(d))),1 + min((max(periods(d)) - duration(x) + 1),p2)):
                var_name1 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p1)
                tmp = Or(tmp,pd[var_name1])
            constraint_1_2 = And(constraint_1_2,Implies(pd[var_name2], tmp))


# In[172]:


# V2.1
for x in tsgn:
    for d in day_list:
        var_name = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)
        pd[var_name] = Bool(var_name)


# In[173]:


# C2.1
constraint_2_1 = True
for x in tsgn:
    for d in day_list:
        var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)
        for p in periods(d): 
            var_name1 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)
            constraint_2_1 = And(constraint_2_1,Implies(pd[var_name1], pd[var_name2]))


# In[174]:


# C2.2
constraint_2_2 = True
tmp_true = True
tmp_false = False
for x in tsgn:
    for d in day_list:
        tmp = copy.deepcopy(tmp_false)
        var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)
        for p1 in periods(d):
            var_name1 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p1)
            tmp = Or(tmp,pd[var_name1])
        constraint_2_2 = And(constraint_2_2,Implies(pd[var_name2], tmp))


# In[175]:


# C2.3
constraint_2_3 = True
for x in tsgn:
    for d in day_list:
        var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)
        for p in range(min(periods(d)), 1 + max(periods(d)) - duration(x) + 1):
            var_name1 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)
            constraint_2_3 = And(constraint_2_3,Implies(pd[var_name1], pd[var_name2]))


# In[176]:


# C2.4
constraint_2_4 = True
tmp_true = True
tmp_false = False
for x in tsgn:
    for d in day_list:
        tmp = copy.deepcopy(tmp_false)
        var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)
        for p1 in range(min(periods(d)), 1 + max(periods(d)) - duration(x) + 1):
            var_name1 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p1)
            tmp = Or(tmp,pd[var_name1])
        constraint_2_4 = And(constraint_2_4,Implies(pd[var_name2], tmp))


# In[177]:


# V3.1
for t in range(len(faculty_list)):
    for d in day_list:
        for p in periods(d):
            var_name = "x"+"t"+str(t)+"d"+str(d)+"p"+str(p)
            pd[var_name] = Bool(var_name)


# In[178]:


# C3.1
constraint_3_1 = True
for x in tsgn:
    for d in day_list:
        for p in periods(d): 
            var_name1 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)
            var_name2 = "x"+"t"+str(x[0])+"d"+str(d)+"p"+str(p)
            constraint_3_1 = And(constraint_3_1,Implies(pd[var_name1], pd[var_name2]))


# In[179]:


# C3.2
constraint_3_2 = True
tmp_true = True
tmp_false = False
for t in range(len(faculty_list)):
    for d in day_list:
        for p in periods(d): 
            tmp = copy.deepcopy(tmp_false)
            var_name2 = "x"+"t"+str(t)+"d"+str(d)+"p"+str(p)
            for x in lessons_t(t):
                var_name1 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p1)
                tmp = Or(tmp,pd[var_name1])
            constraint_3_2 = And(constraint_3_2,Implies(pd[var_name2], tmp))


# In[180]:


# V4.1
for g in batch_list:
    for d in day_list:
        for p in periods(d):
            var_name = "x"+"g"+str(g)+"d"+str(d)+"p"+str(p)
            pd[var_name] = Bool(var_name)


# In[181]:


# C4.1
constraint_4_1 = True
for x in tsgn:
    for d in day_list:
        for p in periods(d): 
            var_name1 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)
            var_name2 = "x"+"g"+str(x[2])+"d"+str(d)+"p"+str(p)
            constraint_4_1 = And(constraint_3_1,Implies(pd[var_name1], pd[var_name2]))


# In[182]:


# C4.2
constraint_4_2 = True
tmp_true = True
tmp_false = False
for g in batch_list:
    for d in day_list:
        for p in periods(d): 
            tmp = copy.deepcopy(tmp_false)
            var_name2 = "x"+"g"+str(x[2])+"d"+str(d)+"p"+str(p)
            for x in lessons_g(g):
                var_name1 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)
                tmp = Or(tmp,pd[var_name1])
            constraint_4_2 = And(constraint_4_2,Implies(pd[var_name2], tmp))


# In[183]:


# C5.1
constraint_5_1 = True
tmp_true = True
tmp_false = False
for x in tsgn:
    tmp = copy.deepcopy(tmp_false)
    for d in day_list:
        var_name = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)
        tmp = Or(tmp,pd[var_name])
    constraint_5_1 = And(constraint_5_1,tmp)


# In[184]:


# C5.2
constraint_5_2 = True
tmp_true = True
tmp_false = False
for x in tsgn:
    for d in day_list:
        tmp = copy.deepcopy(tmp_false)
        var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)
        for p1 in range(min(periods(d)), 1 + max(periods(d)) - duration(x) + 1):
            var_name1 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p1)
            tmp = Or(tmp,pd[var_name1])
        constraint_5_2 = And(constraint_5_2,Implies(pd[var_name2], tmp))


# In[185]:


# C6.1
constraint_6_1 = True
tmp_true = True
tmp_false = False
for x in tsgn:
    tmp = copy.deepcopy(tmp_true)
    for di in range(len(day_list)-1):
        for dj in range(di+1,len(day_list)):
            var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(day_list[di])
            var_name1 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(day_list[dj])
            tmp = And(tmp,Or(Not(pd[var_name1]),Not(pd[var_name2])))
    constraint_6_1 = And(constraint_6_1,tmp)


# In[186]:


# C6.2
constraint_6_2 = True
tmp_true = True
tmp_false = False
for x in tsgn:
    for d in day_list:
        tmp = copy.deepcopy(tmp_true)
        for p1 in range(min(periods(d)), 1 + max(periods(d)) - duration(x) + 1): 
            for p2 in range(p1+1,1 + max(periods(d)) - duration(x) + 1):
                var_name2 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p1)
                var_name1 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p2)
                tmp = And(tmp,Or(Not(pd[var_name1]),Not(pd[var_name2])))
        constraint_6_2 = And(constraint_6_2,tmp)


# In[187]:


# C7.1
constraint_7_1 = True
tmp_true = True
tmp_false = False
for g in batch_list:
    for d in day_list:
        for p in periods(d):
            tmp = copy.deepcopy(tmp_true)
            lg = lessons_g(g) # Lessons of batch g
            for xi in range(len(lg)-1):
                for xj in range(xi+1,len(lg)):
                    x1 = lg[xi]
                    x2 = lg[xj]
                    var_name2 = "x"+"t"+str(x1[0])+"s"+str(x1[1])+"g"+str(x1[2])+"n"+str(x1[3])+"d"+str(d)+"p"+str(p)
                    var_name1 = "x"+"t"+str(x2[0])+"s"+str(x2[1])+"g"+str(x2[2])+"n"+str(x2[3])+"d"+str(d)+"p"+str(p)
                    tmp = And(tmp,Or(Not(pd[var_name1]),Not(pd[var_name2])))
            constraint_7_1 = And(constraint_7_1,tmp)


# In[188]:


# C7.2
constraint_7_2 = True
tmp_true = True
tmp_false = False
for t in range(len(faculty_list)):
    for d in day_list:
        for p in periods(d):
            tmp = copy.deepcopy(tmp_true)
            lt = lessons_t(t) # Lessons of teacher t
            for xi in range(len(lt)-1):
                for xj in range(xi+1,len(lt)):
                    x1 = lg[xi]
                    x2 = lg[xj]
                    var_name2 = "x"+"t"+str(x1[0])+"s"+str(x1[1])+"g"+str(x1[2])+"n"+str(x1[3])+"d"+str(d)+"p"+str(p)
                    var_name1 = "x"+"t"+str(x2[0])+"s"+str(x2[1])+"g"+str(x2[2])+"n"+str(x2[3])+"d"+str(d)+"p"+str(p)
                    tmp = And(tmp,Or(Not(pd[var_name1]),Not(pd[var_name2])))
            constraint_7_2 = And(constraint_7_2,tmp)


# In[189]:


# This function will take a tuple (t,s,g,n) and return the list of indices of room which is of type st, where st is the room type
# of course s

def rooms(x_tsgn):
    x_room_type = course_list[x_tsgn[1]][1]
    x_room_list = type_to_room_dict[x_room_type]
    return [room_to_index[x] for x in x_room_list]


# In[190]:


rooms((1, 0, 2, 1))


# In[191]:


# V5.1
for x in tsgn:
    for d in day_list:
        for p in range(min(periods(d)), 1 + max(periods(d)) - duration(x) + 1):
            for r in rooms(x):
                var_name = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)+"r"+str(r)
                pd[var_name] = Bool(var_name)


# In[192]:


# V5.2
for x in tsgn:
    for d in day_list:
        for p in range(min(periods(d)), 1 + max(periods(d))):
            for r in rooms(x):
                var_name = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)+"r"+str(r)
                pd[var_name] = Bool(var_name)


# In[193]:


# C9.1
constraint_9_1 = True
for x in tsgn:
    for d in day_list:
        for r in rooms(x):
            for p1 in range(min(periods(d)), 1 + max(periods(d)) - duration(x) + 1): 
                for p2 in range(p1,1 + p1 + duration(x) - 1):
                    var_name1 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p1)+"r"+str(r)
                    var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p2)+"r"+str(r)
                    constraint_9_1 = And(constraint_9_1,Implies(pd[var_name1], pd[var_name2]))


# In[194]:


# C9.2
constraint_9_2 = True
tmp_true = True
tmp_false = False
for x in tsgn:
    for d in day_list:
        for r in rooms(x):
            for p2 in range(min(periods(d)), 1 + max(periods(d))): 
                tmp = copy.deepcopy(tmp_false)
                var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p2)+"r"+str(r)
                for p1 in range(max(p2 - duration(x) + 1, min(periods(d))),1 + min((max(periods(d)) - duration(x) + 1),p2)):
                    var_name1 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p1)+"r"+str(r)
                    tmp = Or(tmp,pd[var_name1])
                constraint_9_2 = And(constraint_9_2,Implies(pd[var_name2], tmp))


# In[195]:


# C10.1
constraint_10_1 = True
for x in tsgn:
    for d in day_list:
        for p in range(min(periods(d)), 1 + max(periods(d)) - duration(x) + 1): 
            for r in rooms(x):
                var_name1 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)+"r"+str(r)
                var_name2 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)
                constraint_10_1 = And(constraint_10_1,Implies(pd[var_name1], pd[var_name2]))


# In[196]:


# C10.3
constraint_10_3 = True
for x in tsgn:
    for d in day_list:
        for p in periods(d): 
            for r in rooms(x):
                var_name1 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)+"r"+str(r)
                var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)
                constraint_10_3 = And(constraint_10_3,Implies(pd[var_name1], pd[var_name2]))


# In[197]:


# C10.2
constraint_10_2 = True
tmp_true = True
tmp_false = False
for x in tsgn:
    for d in day_list:
        for p in range(min(periods(d)), 1 + max(periods(d)) - duration(x) + 1):
            tmp = copy.deepcopy(tmp_false)
            var_name2 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)
            for r in rooms(x):
                var_name1 = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)+"r"+str(r)
                tmp = Or(tmp,pd[var_name1])
            constraint_10_2 = And(constraint_10_2,Implies(pd[var_name2], tmp))


# In[198]:


# C10.4
constraint_10_4 = True
tmp_true = True
tmp_false = False
for x in tsgn:
    for d in day_list:
        for p in periods(d):
            tmp = copy.deepcopy(tmp_false)
            var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)
            for r in rooms(x):
                var_name1 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)+"r"+str(r)
                tmp = Or(tmp,pd[var_name1])
            constraint_10_4 = And(constraint_10_4,Implies(pd[var_name2], tmp))


# In[199]:


# V6
for t in range(len(faculty_list)):
    for d in day_list:
        for p in periods(d):
            for r in range(len(room_list)):
                var_name = "x"+"t"+str(t)+"d"+str(d)+"p"+str(p)+"r"+str(r)
                pd[var_name] = Bool(var_name)


# In[200]:


# C10.5
constraint_10_5 = True
for t in range(len(faculty_list)):
    for d in day_list:
        for p in periods(d): 
            for r in range(len(room_list)):
                var_name1 = "x"+"t"+str(t)+"d"+str(d)+"p"+str(p)+"r"+str(r)
                var_name2 = "x"+"t"+str(t)+"d"+str(d)+"p"+str(p)
                constraint_10_5 = And(constraint_10_5,Implies(pd[var_name1], pd[var_name2]))


# In[201]:


# C10.6
constraint_10_6 = True
tmp_true = True
tmp_false = False
for t in range(len(faculty_list)):
    for d in day_list:
        for p in periods(d): 
            tmp = copy.deepcopy(tmp_false)
            var_name2 = "x"+"t"+str(t)+"d"+str(d)+"p"+str(p)
            for r in range(len(room_list)):
                var_name1 = "x"+"t"+str(t)+"d"+str(d)+"p"+str(p)+"r"+str(r)
                tmp = Or(tmp,pd[var_name1])
            constraint_10_6 = And(constraint_10_6,Implies(pd[var_name2], tmp))


# In[202]:


# C11.1
constraint_11_1 = True
tmp_true = True
tmp_false = False
for d in day_list:
    for p in periods(d): 
        for r in range(len(room_list)):
            tmp = copy.deepcopy(tmp_true)
            for ti in range(len(faculty_list)-1):
                for tj in range(ti+1,len(faculty_list)):
                    var_name2 = "x"+"t"+str(ti)+"d"+str(d)+"p"+str(p)+"r"+str(r)
                    var_name1 = "x"+"t"+str(tj)+"d"+str(d)+"p"+str(p)+"r"+str(r)
                    tmp = And(tmp,Or(Not(pd[var_name1]),Not(pd[var_name2])))
            constraint_11_1 = And(constraint_11_1,tmp)


# In[203]:


# C11.2
constraint_11_2 = True
tmp_true = True
tmp_false = False
for d in day_list:
    for p in periods(d): 
        for t in range(len(faculty_list)):
            tmp = copy.deepcopy(tmp_true)
            for ri in range(len(room_list)-1):
                for rj in range(ri+1,len(room_list)):
                    var_name2 = "x"+"t"+str(t)+"d"+str(d)+"p"+str(p)+"r"+str(ri)
                    var_name1 = "x"+"t"+str(t)+"d"+str(d)+"p"+str(p)+"r"+str(rj)
                    tmp = And(tmp,Or(Not(pd[var_name1]),Not(pd[var_name2])))
            constraint_11_2 = And(constraint_11_2,tmp)


# In[204]:


# C12.1
constraint_12_1 = True
tmp_true = True
tmp_false = False
for x in tsgn:
    for d in day_list:
        for p in periods(d):
            tmp = copy.deepcopy(tmp_true)
            var_name2 = "x"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)
            # Get faculties of the course s
            x_f_list = course_list[x[1]][3]
            if len(x_f_list) > 1:
                x_f_list = x_f_list[1:]
                t_list = [faculty_to_index[fi] for fi in x_f_list]
                for t in t_list:
                    var_name1 = "x"+"t"+str(t)+"d"+str(d)+"p"+str(p)
                    tmp = And(tmp,Not(pd[var_name1]))
                constraint_10_4 = And(constraint_10_4,Implies(pd[var_name2], tmp))


# In[205]:


ff = True # Final formula
ff = And(ff, constraint_1_1)
ff = And(ff, constraint_1_2)
ff = And(ff, constraint_2_1)
ff = And(ff, constraint_2_2)
ff = And(ff, constraint_2_3)
ff = And(ff, constraint_2_4)
ff = And(ff, constraint_3_1)
ff = And(ff, constraint_3_2)
ff = And(ff, constraint_4_1)
ff = And(ff, constraint_4_2)
ff = And(ff, constraint_5_1)
ff = And(ff, constraint_5_2)
ff = And(ff, constraint_6_1)
ff = And(ff, constraint_6_2)
ff = And(ff, constraint_7_1)
ff = And(ff, constraint_7_2)
ff = And(ff, constraint_9_1)
ff = And(ff, constraint_9_2)
ff = And(ff, constraint_10_1)
ff = And(ff, constraint_10_2)
ff = And(ff, constraint_10_3)
ff = And(ff, constraint_10_4)
ff = And(ff, constraint_10_5)
ff = And(ff, constraint_10_6)
ff = And(ff, constraint_11_1)
ff = And(ff, constraint_11_2)
ff = And(ff, constraint_12_1)

# Solving and creating model
s = Solver()
s.add(ff)
if str(s.check()) == "sat":
    print("There exists a timetable which can satisfy the given constraints")
else :
    print("There doesn't exist a timetable which can satisfy the given constraints")
m = s.model()


# In[206]:


final_timetable = []

for x in tsgn:
    for d in day_list:
        for p in range(min(periods(d)), 1 + max(periods(d)) - duration(x) + 1):
            for r in rooms(x):
                var_name = "xdas"+"t"+str(x[0])+"s"+str(x[1])+"g"+str(x[2])+"n"+str(x[3])+"d"+str(d)+"p"+str(p)+"r"+str(r)
                if (m.evaluate(pd[var_name])) : 
                    final_timetable.append(var_name)


# In[207]:


x_course = []
x_batch = []
x_day = []
x_period = []
x_room = []
x_teacher = []
x_n_th_lecture = []

for each_class in final_timetable:
    indx_t = each_class.find("t")
    indx_s = each_class.find("s",4)
    indx_g = each_class.find("g")
    indx_n = each_class.find("n")
    indx_d = each_class.find("d",3)
    indx_p = each_class.find("p")
    indx_r = each_class.find("r")

    x_course.append(int(each_class[indx_s+1:indx_g]))
    x_batch.append(int(each_class[indx_g+1:indx_n])) 
    x_day.append(int(each_class[indx_d+1:indx_p]))
    x_period.append(int(each_class[indx_p+1:indx_r]))
    x_room.append(int(each_class[indx_r+1:]))
    x_teacher.append(int(each_class[indx_t+1:indx_s]))
    x_n_th_lecture.append(int(each_class[indx_n+1:indx_d]))

import pandas as pd

df = pd.DataFrame({
    'Course' : pd.Series(x_course),
    'Batch' : pd.Series(x_batch),
    'Day' : pd.Series(x_day),
    'Period' : pd.Series(x_period),
    'Room' : pd.Series(x_room),
    'Teacher': pd.Series(x_teacher),
    'n_th_lec': pd.Series(x_n_th_lecture)
})

df = df.sort_values(by=['Day', 'Period','Batch','Room'])


# In[208]:


from beautifultable import BeautifulTable
timeTable = BeautifulTable()
timeTable.column_headers = ["COURSE", "BATCH", "DAY","TIME","VENUE","FACULTY"]

period_to_time_if_morning = {1:"8:30 am - 9:00 am",2:"9:00 am - 9:30 am",3:"9:30 am - 10:00 am",4:"10:00 am - 10:30 am",5:"10:30 am - 11:00 am",6:"11:00 am - 11:30 am",7:"11:30 am - 12:00 pm",8:"12:00 pm - 12:30 pm"}
period_to_time_if_evening = {1:"2:00 pm - 2:30 pm",2:"2:30 pm - 3:00 pm",3:"3:00 pm - 3:30 pm",4:"3:30 pm - 4:00 pm",5:"4:00 pm - 4:30 pm",6:"4:30 pm - 5:00 pm"}

print("\n\n******************************** FINAL TIMETABLE SCHEDULED *******************************\n\n")

def final_scheduling_of_entire_timetable(final_timetable):
    
    for index, row in df.iterrows():
    
        x_teacher = row['Teacher']
        x_course = row['Course']
        x_batch = row['Batch']
        x_n_th_lecture = row['n_th_lec']
        x_day = row['Day']
        x_period = row['Period']
        x_room = row['Room']
        
        x_day_To_day = {1:'Monday',2:'Monday',3:'Tuesday',4:'Tuesday',5:'Wednesday',6:'Wednesday',7:'Thursday',8:'Thursday',9:'Friday',10:'Friday'}
        
        time_of_course = ""
        
        if x_day % 2 == 0 : # If it is "Evening" Session
            duration_of_lecture = duration((x_teacher,x_course,x_batch,x_n_th_lecture))
            st_dash_index = period_to_time_if_evening[x_period].find("-")
            start_time = period_to_time_if_evening[x_period][:st_dash_index]
            et_dash_index = period_to_time_if_evening[x_period+duration_of_lecture-1].find("-")
            end_time = period_to_time_if_evening[x_period+duration_of_lecture-1][et_dash_index+1:]
            time_of_course = start_time + "-" + end_time
        
        else : # If it is "Morning" Session"
            duration_of_lecture = duration((x_teacher,x_course,x_batch,x_n_th_lecture))
            st_dash_index = period_to_time_if_morning[x_period].find("-")
            start_time = period_to_time_if_morning[x_period][:st_dash_index]
            et_dash_index = period_to_time_if_morning[x_period+duration_of_lecture-1].find("-")
            end_time = period_to_time_if_morning[x_period+duration_of_lecture-1][et_dash_index+1:]
            time_of_course = start_time + "-" + end_time 
        
        facutlies_for_this_course = ",".join(course_list[x_course][3])
        timeTable.append_row([course_list[x_course][0], x_batch, x_day_To_day[x_day],time_of_course,room_list[x_room],facutlies_for_this_course])

# Final Execution for printing the Time Table scheduled
final_scheduling_of_entire_timetable(final_timetable)
print(timeTable)


# In[209]:


with open('timeTable.txt','w') as f:
    f.write("\n\n******************************** FINAL TIMETABLE SCHEDULED *******************************\n\n")
    f.write(str(timeTable))


# In[210]:


print("Execution Time :",time.time() - start_time_of_program)

