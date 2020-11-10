#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Aug  6 15:43:43 2020
@author: Tristan
"""





# Program outline
# Done: Import data
# Done: If desired, have the ability to cut out some of the data
# Done: Find all order sequences
# Done: Dominate order sequences
# Done: Find all sequence-restaurant pairs
# Done: Dominate sequence-restaurant pairs
# Done: Create untimed arcs
# Done: Create model nodes
# Done: Convert untimed arcs to timed arcs
# Done: Add model variables
# Done: Add model constraints
# Done: Solve linear model
# Done: Add valid inequality cuts
# Done: Solve integer model
# TODO: Add illegal path elimination constraints in callback

# Improvements:
# TODO: Merge sequence-restaurant pair generation with sequence generation
# TODO: Put sequence + pair domination into the one function
# TODO: Properly remove arcs that go backwards in time
# TODO: Properly remove duplicate on-off arcs
# TODO: Properly remove arcs that go to the same node as they left
# TODO: Remove or formalise home -> home arcs
# TODO: Revise code to ensure correctness
# TODO: Confirm that VI cuts aren't causing a problem
# TODO: Add an entry untimed arc for every courier, not just every group
# TODO: Find out why non-global node times is infeasible





import math
from collections import defaultdict
import itertools
from time import time
from gurobi import Model, quicksum, GRB
import random
from operator import lt, gt





courierData = {} # courier: [x, y, ontime, offtime]
orderData = {} # order: [x, y, placementtime, restaurant, readytime, latestLeavingTime, maxClickToDoorArrivalTime]
restaurantData = {} # restaurant: [x, y]





sequenceData = {} # orderSequence: [placementRestaurant, earliestDepartureTime, latestDepartureTime, totalTravelTime]
sequenceNextRestaurantData = {} # (sequence, nextRestaurant): [placementRestaurant, earliestDepartureTime, latestDepartureTime, totalTravelTime]
untimedArcData = {} # (courierGroup, sequence, nextRestaurant): [placementRestaurant, earliestDepartureTime, latestDepartureTime, totalTravelTime]





grubhubInstance = '0o50t100s1p125'
fileDirectory = 'MealDeliveryRoutingGithub/public_instances/' + grubhubInstance + '/'
programStartTime = time()





nodeTimeInterval = 8 # minutes between nodes
groupCouriersByOffTime = True
orderProportion = 1
seed = 1
globalNodeIntervals = True





def WithoutLetters(string):
    return string.translate({ord(i): None for i in 'abcdefghijklmnopqrstuvwxyz'})





def OpenFile(fileName):
    with open(fileDirectory + fileName) as file:
        # Get lines, dropping header line
        lines = file.read().splitlines()[1:]
        dataDictionary = {}
        for line in lines:
            data = map(WithoutLetters, line.split('\t'))
            data = list(map(int, data))
            dataDictionary[data[0]] = data[1:]
        return dataDictionary





courierData = OpenFile('couriers.txt')
orderData = OpenFile('orders.txt')
restaurantData = OpenFile('restaurants.txt')
print(str(len(courierData)) + ' couriers')
print(str(len(orderData)) + ' orders')
print(str(len(restaurantData)) + ' restaurants')





def GiveMeAStatusUpdate(label, collectionToDisplayLengthOf):
    print(str(len(collectionToDisplayLengthOf)) + ' ' + label + ' ' + str(time() - programStartTime))





with open(fileDirectory + 'instance_parameters.txt') as instanceParameters:
    instanceParameters.readline().strip()
    parameters = instanceParameters.readline().strip().split('\t')
    travelSpeed = int(parameters[0]) # metres per minute
    pickupServiceTime = int(parameters[1]) # minutes
    dropoffServiceTime = int(parameters[2]) # minutes
    targetClickToDoor = int(parameters[3]) # minutes
    maxClickToDoor = int(parameters[4]) # minutes
    payPerDelivery = int(parameters[5]) # dollars
    minPayPerHour = int(parameters[6]) # dollars





ordersAtRestaurant = {restaurant: [] for restaurant in restaurantData}
for order in orderData:
    ordersAtRestaurant[orderData[order][3]].append(order)





if orderProportion < 1.0:
    random.seed(seed)
    totalOrderCount = len(orderData)
    restaurantsRemoved = []
    while len(orderData) > totalOrderCount * orderProportion:
        removedRestaurant = random.choice(list(restaurantData.keys()))
        for order in ordersAtRestaurant[removedRestaurant]:
            del orderData[order]
        del ordersAtRestaurant[removedRestaurant]
        del restaurantData[removedRestaurant]
        restaurantsRemoved.append(removedRestaurant)
    print()
    print('Seed = ' + str(seed))
    print('Removed restaurants ' + str(restaurantsRemoved))
    print('Now at ' + str(len(orderData)) + ' orders, down from ' + str(totalOrderCount))
    print()
        




courierGroups = {}
if groupCouriersByOffTime:
    for courier in courierData:
        offTime = courierData[courier][3]
        if offTime not in courierGroups:
            courierGroups[offTime] = [[], offTime]
        courierGroups[offTime][0].append(courier)
else:
    for courier in courierData:
        courierGroups[courier] = [[courier], courierData[courier][3]]
globalOffTime = max(courierGroups[group][1] for group in courierGroups)





def TravelTime(loc1, loc2):
    x1, y1 = loc1[0], loc1[1]
    x2, y2 = loc2[0], loc2[1]
    return math.sqrt((x1-x2)**2 + (y1-y2)**2) / travelSpeed





for order in orderData:
    maxClickToDoorArrivalTime = orderData[order][2] + maxClickToDoor
    travelTime = (pickupServiceTime + dropoffServiceTime) / 2 + TravelTime(restaurantData[orderData[order][3]], orderData[order])
    orderData[order].append(maxClickToDoorArrivalTime - travelTime)
    orderData[order].append(maxClickToDoorArrivalTime)





def CompareOneIndex(op, dictionary, key1, key2, index):
    return op(dictionary[key1][index], dictionary[key2][index])





def CompareTwoIndices(op1, op2, dictionary, key1, key2, index1, index2):
    return CompareOneIndex(op1, dictionary, key1, key2, index1) and CompareOneIndex(op2, dictionary, key1, key2, index2)





def RemoveDominatedSequences(sequences):
    sequencesBySetAndLastOrder = defaultdict(list)
    for sequence in sequences:
        sequencesBySetAndLastOrder[(frozenset(sequence), sequence[-1])].append(sequence)
    sequencesBySetAndLastOrder = dict(sequencesBySetAndLastOrder)
    dominatedSequences = set()
    for group in sequencesBySetAndLastOrder:
        if len(sequencesBySetAndLastOrder[group]) > 1:
            for (sequence1, sequence2) in itertools.combinations(sequencesBySetAndLastOrder[group],2):
                if CompareTwoIndices(gt, lt, sequences, sequence1, sequence2, 2, 3):
                    dominatedSequences.add(sequence2)
                elif CompareTwoIndices(lt, gt, sequences, sequence1, sequence2, 2, 3):
                    dominatedSequences.add(sequence1)
    for sequence in dominatedSequences:
        del sequences[sequence]
    return sequences





# Calculate & dominate order sequences
for restaurant in restaurantData:
    sequenceLength = 1
    calculatedSequences = {}
    for order in ordersAtRestaurant[restaurant]:
        calculatedSequences[(order,)] = [restaurant, orderData[order][4], orderData[order][5], TravelTime(restaurantData[restaurant], orderData[order]) + (pickupServiceTime + dropoffServiceTime) / 2]
    for sequence in calculatedSequences:
        sequenceData[sequence] = calculatedSequences[sequence]
    while len(calculatedSequences) > 0:
        sequenceLength += 1
        newSequences = {}
        for sequence in calculatedSequences:
            for order in ordersAtRestaurant[restaurant]:
                if order not in sequence:
                    newSequence = sequence + (order,)
                    totalTravelTime = sequenceData[sequence][3] + dropoffServiceTime + TravelTime(orderData[sequence[-1]], orderData[order])
                    latestLeavingTime = min(sequenceData[sequence][2], orderData[order][6] - totalTravelTime)
                    earliestLeavingTime = max(sequenceData[sequence][1], orderData[order][4])
                    if earliestLeavingTime <= latestLeavingTime:
                        newSequences[newSequence] = [restaurant, earliestLeavingTime, latestLeavingTime, totalTravelTime]
        if sequenceLength >= 3:
            newSequences = RemoveDominatedSequences(newSequences)
        calculatedSequences = newSequences
        for sequence in calculatedSequences:
            sequenceData[sequence] = calculatedSequences[sequence]
        if len(calculatedSequences) == 0:
            break





sequencesByRestaurantThenOrderSet = {}
for sequence in sequenceData:
    restaurant = sequenceData[sequence][0]
    if restaurant not in sequencesByRestaurantThenOrderSet:
        sequencesByRestaurantThenOrderSet[restaurant] = defaultdict(list)
    sequencesByRestaurantThenOrderSet[restaurant][frozenset(sequence)].append(sequence)
GiveMeAStatusUpdate('delivery sequences', sequenceData)





def CheckDominationPairs(sequenceToCheck, nextRestaurant):
    dominatedSequences = []
    for sequence in groupedPairs[(frozenset(sequenceToCheck), nextRestaurant)]:
        if sequence != sequenceToCheck:
            if CompareTwoIndices(lt, gt, sequenceNextRestaurantData, (sequenceToCheck, nextRestaurant), (sequence, nextRestaurant), 2, 3):
                return [sequenceToCheck]
            if CompareTwoIndices(gt, lt, sequenceNextRestaurantData, (sequenceToCheck, nextRestaurant), (sequence, nextRestaurant), 2, 3):
                dominatedSequences.append(sequence)
    return dominatedSequences





groupedPairs = defaultdict(list) # (frozenset(sequence), nextRestaurant): [sequence1, sequence2, sequence3, ...]
for sequence in sequenceData:
    finishTime = sequenceData[sequence][1] + sequenceData[sequence][3]
    for restaurant in restaurantData:
        arrivalAtRestaurant = finishTime + TravelTime(orderData[sequence[-1]], restaurantData[restaurant]) + (dropoffServiceTime + pickupServiceTime) / 2
        for order in ordersAtRestaurant[restaurant]:
            if orderData[order][5] > arrivalAtRestaurant:
                travelTime = sequenceData[sequence][3] + TravelTime(orderData[sequence[-1]], restaurantData[restaurant]) + (dropoffServiceTime + pickupServiceTime) / 2
                sequenceNextRestaurantData[(sequence, restaurant)] = sequenceData[sequence][:3] + [travelTime]
                groupedPairs[(frozenset(sequence), restaurant)].append(sequence)
                dominatedSequences = CheckDominationPairs(sequence, restaurant)
                for dominatedSequence in dominatedSequences:
                    del sequenceNextRestaurantData[(dominatedSequence, restaurant)]
                    groupedPairs[(frozenset(sequence), restaurant)].remove(dominatedSequence)
                break
groupedPairs = dict(groupedPairs)
GiveMeAStatusUpdate('post-domination pairs', sequenceNextRestaurantData)





untimedArcs = set() # {(offTime1, sequence1, nextRestaurant1), (offTime2, sequence2, nextRestaurant2), ...}
# Main untimedArcs
# Create (courierGroup, orderSequence, nextRestaurant) triples
# Loop through (orderSequence, nextRestaurant) pairs, and loop through groups, checking to see if valid together
# Valid if:
# 1. earliest leaving time is before the group's off time
# 2. courier can arrive at restaraunt before off time
# 3. courier can arrive at restaurant before latest leaving time
# 4. the arrival at the next restaurant is before the group's off time
# 5. there is at least one order at the next restaurant that is deliverable between the courier's arrival and the group's off time
# 6. the earliest leaving time plus the travel time is before the group's off time (less refined version of 4)
for sequence, nextRestaurant in sequenceNextRestaurantData:
    restaurant, earliestLeavingTime, latestLeavingTime, travelTime = sequenceNextRestaurantData[sequence, nextRestaurant]
    for group in courierGroups:
        offTime = courierGroups[group][1]
        if offTime >= earliestLeavingTime + travelTime: # check conditions 1, 6
            foundValidCourier = False
            bestArrivalTime = globalOffTime
            for courier in courierGroups[group][0]:
                commute = TravelTime(courierData[courier], restaurantData[restaurant]) + pickupServiceTime / 2
                arrivalAtDepartureRestaurant = courierData[courier][2] + commute
                if arrivalAtDepartureRestaurant <= min(latestLeavingTime, offTime): # check conditions 2 and 3
                    foundValidCourier = True
                    if arrivalAtDepartureRestaurant < bestArrivalTime:
                        bestArrivalTime = arrivalAtDepartureRestaurant
            if foundValidCourier:
                earliestDepartureFromDepartureRestaurant = max(bestArrivalTime, earliestLeavingTime) # can't leave before arrive
                if earliestDepartureFromDepartureRestaurant > latestLeavingTime:
                    print('Main untimed arc error 1!', str(group), str(sequence), str(nextRestaurant))
                arrivalAtNextRestaurant = earliestDepartureFromDepartureRestaurant + travelTime
                if arrivalAtNextRestaurant <= offTime: # check condition 4
                    foundValidOrder = False
                    bestOrderLatestLeavingTime = 0
                    for order in ordersAtRestaurant[nextRestaurant]:
                        if orderData[order][4] <= offTime and orderData[order][5] >= arrivalAtNextRestaurant:
                            foundValidOrder = True
                            if orderData[order][5] > bestOrderLatestLeavingTime:
                                bestOrderLatestLeavingTime = orderData[order][5]
                    if foundValidOrder: # check condition 5
                        latestArrivalAtNextRestaurant = min(bestOrderLatestLeavingTime, offTime)
                        latestDepartureAtDepartureRestaurant = latestArrivalAtNextRestaurant - travelTime
                        if latestDepartureAtDepartureRestaurant < earliestDepartureFromDepartureRestaurant:
                            print('Main untimed arc error 2!', str(group), str(sequence), str(nextRestaurant))
                        untimedArcs.add((group, sequence, nextRestaurant))
                        untimedArcData[(group, sequence, nextRestaurant)] = [restaurant, earliestDepartureFromDepartureRestaurant, latestDepartureAtDepartureRestaurant, travelTime]
GiveMeAStatusUpdate('main untimedArcs', untimedArcs)





# Exit untimedArcs
# Create sequence-courier (off time) pairs, with nextRestaurant = 0
# An untimed exit arc is of the form (group, sequence, 0)
# Iterate through all group, sequence pairs, checking if compatible:
# - Earliest leaving time must be before the group's off time
# - At least one courier can arrive at the restaurant before off time
# - Out of those couriers, at least one must arrive before latest leaving time
exitUntimedArcsByCourierRestaurant = defaultdict(list)
for sequence in sequenceData:
    restaurant, earliestLeavingTime, latestLeavingTime, totalTravelTime = sequenceData[sequence]
    for group in courierGroups:
        offTime = courierGroups[group][1]
        if offTime >= earliestLeavingTime: # sequence must be deliverable in courier's shift
            foundValidCourier = False
            bestArrivalTime = globalOffTime
            for courier in courierGroups[group][0]:
                commute = TravelTime(courierData[courier], restaurantData[restaurant]) + pickupServiceTime / 2
                arrivalTime = courierData[courier][2] + commute
                if arrivalTime <= min(offTime, latestLeavingTime): # courier must arrive at restaurant in-shift, and in time to pick up and deliver order
                    foundValidCourier = True
                    bestArrivalTime = min(arrivalTime, bestArrivalTime)
            if foundValidCourier: # only add arc if valid courier found, add data for best courier found
                untimedArcs.add((group, sequence, 0))
                untimedArcData[(group, sequence, 0)] = [restaurant, max(earliestLeavingTime, bestArrivalTime), min(latestLeavingTime, offTime), totalTravelTime]
                exitUntimedArcsByCourierRestaurant[(group, restaurant)].append((group, sequence, 0))
exitUntimedArcsByCourierRestaurant = dict(exitUntimedArcsByCourierRestaurant)
GiveMeAStatusUpdate('main + exit untimedArcs', untimedArcs)





# Entry untimedArcs
# An entry untimed arc is of the form (courierGroup, (), restaurant)
# Iterate through courier groups and restaurants, finding compatible pairs
# Compatible if:
# - can arrive at restaurant before off time
# - there is at least one order at the restaurant such that:
#   - the latest leaving time for the order is after at least one courier's on time
#   - the order ready time is before the group's off time
for group in courierGroups:
    offTime = courierGroups[group][1]
    for restaurant in restaurantData:
        foundValidCourier = False
        bestArrival = globalOffTime
        bestCourier = 0
        for courier in courierGroups[group][0]:
            commute = TravelTime(courierData[courier], restaurantData[restaurant]) + pickupServiceTime / 2
            arrivalTime = courierData[courier][2] + commute
            if arrivalTime <= offTime:
                foundValidCourier = True
                if arrivalTime < bestArrival:
                    bestArrival = arrivalTime
                    travelTime = commute
                    bestCourier = courier
        if foundValidCourier:
            latestArrival = 0
            foundValidOrder = False
            for order in ordersAtRestaurant[restaurant]:
                if orderData[order][4] <= offTime and orderData[order][5] >= bestArrival:
                    latestArrival = max(latestArrival, orderData[order][5])
                    foundValidOrder = True
            if foundValidOrder:
                earliestLeavingTime = courierData[bestCourier][2]
                latestLeavingTime = max(latestArrival, offTime) - commute
                if latestLeavingTime < earliestLeavingTime:
                    print('Error! Invalid untimed arc:', str(group), str(restaurant))
                untimedArcs.add((group, (), restaurant))
                untimedArcData[(group, (), restaurant)] = [0, earliestLeavingTime, latestLeavingTime, commute]
GiveMeAStatusUpdate('all untimedArcs', untimedArcs)





untimedArcsByCourierRestaurant = defaultdict(list)
# (offTime, departureRestaurant): [(offTime, sequence1, nextRestaurant1), (offTime, sequence2, nextRestaurant2), ...]
untimedArcsByCourierNextRestaurant = defaultdict(list)
for arc in untimedArcs:
    if arc[1] == ():
        untimedArcsByCourierRestaurant[(arc[0], 0)].append(arc)
    else:
        untimedArcsByCourierRestaurant[(arc[0], orderData[arc[1][0]][3])].append(arc)
    untimedArcsByCourierNextRestaurant[(arc[0], arc[2])].append(arc)
untimedArcsByCourierRestaurant = dict(untimedArcsByCourierRestaurant)
untimedArcsByCourierNextRestaurant = dict(untimedArcsByCourierNextRestaurant)





nodesInModel = set()
# {(offTime1, restaurant1, time1), (offTime2, restaurant2, time2), ...}
nodeTimesByCourierRestaurant = defaultdict(list)
if globalNodeIntervals:
    nodeTimes = list(i for i in range(0, globalOffTime + 1, nodeTimeInterval))   
    for group, restaurant in untimedArcsByCourierRestaurant:
        if restaurant != 0:
            earliestArrivalTime = min(courierData[c][2] + TravelTime(courierData[c], restaurantData[restaurant]) for c in courierGroups[group][0])
            earliestArrivalTime += pickupServiceTime / 2
            groupOffTime = courierGroups[group][1]
            firstLeavingTime = max(min(untimedArcData[i][1] for i in untimedArcsByCourierRestaurant[group, restaurant]), earliestArrivalTime)
            lastLeavingTime = min(max(untimedArcData[i][2] for i in untimedArcsByCourierRestaurant[group, restaurant]), globalOffTime)
            firstNodeTime = max(i for i in nodeTimes if i <= firstLeavingTime)
            nodeTime = firstNodeTime
            while nodeTime <= lastLeavingTime:
                nodesInModel.add((group, restaurant, nodeTime))
                nodeTimesByCourierRestaurant[(group, restaurant)].append(nodeTime)
                nodeTime += nodeTimeInterval
else:
    for group in courierGroups:
        offTime = courierGroups[group][1]
        for restaurant in restaurantData:
            earliestArrivalTime = min(courierData[courier][2] + TravelTime(courierData[courier], restaurantData[restaurant]) + pickupServiceTime / 2 for courier in courierGroups[group][0])
            if earliestArrivalTime > offTime:
                continue
            deliverableOrders = set(order for order in ordersAtRestaurant[restaurant] if orderData[order][4] <= offTime and orderData[order][5] >= earliestArrivalTime)
            if len(deliverableOrders) == 0:
                continue
            latestNodeTime = min(max(orderData[order][5] for order in deliverableOrders), offTime)
            earliestNodeTime = max(min(orderData[order][4] for order in deliverableOrders), earliestArrivalTime)
            if earliestNodeTime > latestNodeTime:
                print('error!', group, restaurant, earliestNodeTime, latestNodeTime, earliestArrivalTime)
            nodeTime = earliestNodeTime
            while nodeTime <= latestNodeTime:
                nodesInModel.add((group, restaurant, nodeTime))
                nodeTimesByCourierRestaurant[(group, restaurant)].append(nodeTime)
                nodeTime += nodeTimeInterval
GiveMeAStatusUpdate('nodes generated', nodesInModel)
for group in courierGroups:
    nodesInModel.add((group, 0, 0))
    nodesInModel.add((group, 0, globalOffTime))
    nodeTimesByCourierRestaurant[(group, 0)] = [0, globalOffTime]
nodeTimesByCourierRestaurant = dict(nodeTimesByCourierRestaurant)





nodesByOfftimeRestaurantPair = defaultdict(list)
# (offTime, departureRestaurant): [(offTime, departureRestaurant, time1), (offTime, departureRestaurant, time2), ...]
for node in nodesInModel:
    nodesByOfftimeRestaurantPair[node[:2]].append(node)
nodesByOfftimeRestaurantPair = dict(nodesByOfftimeRestaurantPair)
timedArcs = set()
# An arc is defined by a (courierOffTime, restaurant1, time1, orderSequence, restaurant2, time2) sextuple
# time2 is a function of time1, orderSequence, restaurant2
for (g, s, r2) in untimedArcData:
    if s != ():
        offTime = courierGroups[g][1]
        r1, earliestLeavingTime, latestLeavingTime, travelTime = untimedArcData[g,s,r2]
        nodeTimesAtLeavingRestaurant = nodeTimesByCourierRestaurant[(g, r1)]
        nodeTimesAtArrivingRestaurant = nodeTimesByCourierRestaurant[(g, r2)]
        nodeTimesAtLeavingRestaurant.sort()
        nodeTimesAtArrivingRestaurant.sort()
        if min(nodeTimesAtLeavingRestaurant) <= earliestLeavingTime:
            firstArcLeavingTime = max(i for i in nodeTimesAtLeavingRestaurant if i <= earliestLeavingTime)
        else:
            if min(nodeTimesAtLeavingRestaurant) > latestLeavingTime:
                break
            else:
                firstArcLeavingTime = min(nodeTimesAtLeavingRestaurant)
        currentNodeTime = firstArcLeavingTime
        while currentNodeTime <= latestLeavingTime:
            arrivalAtNextRestaurant = max(currentNodeTime, earliestLeavingTime) + travelTime
            if r2 != 0:
                if arrivalAtNextRestaurant > max(nodeTimesAtArrivingRestaurant):
                    break
                potentialArrivalTimes = []
                for nodeTime in nodeTimesAtArrivingRestaurant:
                    if nodeTime <= arrivalAtNextRestaurant and nodeTime > currentNodeTime:
                        potentialArrivalTimes.append(nodeTime)
                if len(potentialArrivalTimes) > 0:
                    arrivalNodeTime = max(potentialArrivalTimes)
                else:
                    arrivalNodeTime = min(i for i in nodeTimesAtArrivingRestaurant if i > currentNodeTime)
            else:
                arrivalNodeTime = globalOffTime
            timedArcs.add((g, r1, currentNodeTime, s, r2, arrivalNodeTime))
            currentNodeTime += nodeTimeInterval
    else:
        arrivalNodeTime = min(nodeTimesByCourierRestaurant[(g, r2)])
        timedArcs.add((g, 0, 0, (), r2, arrivalNodeTime))





# Waiting arcs
def NodeTime(node):
    return node[2]
for pair in nodesByOfftimeRestaurantPair:
    nodeList = nodesByOfftimeRestaurantPair[pair]
    if len(nodeList) > 0:
        nodeList.sort(key = NodeTime)
        for i in range(1, len(nodeList)):
            timedArcs.add((pair[0], pair[1], nodeList[i-1][2], (), pair[1], nodeList[i][2]))
GiveMeAStatusUpdate('timed arcs', timedArcs)





print()
m = Model('MDRP')
m.setParam('Method', 2)





arcsByDepartureNode = defaultdict(list) # (c,r1,t1): [timedArc1, timedArc2, ...]
arcsByArrivalNode = defaultdict(list) # (c,r2,t2): [timedArc1, timedArc2, ...]
arcsByCourier = defaultdict(list) # c: [timedArc1, timedArc2, ...]
arcsByOrder = {o: [] for o in orderData}
outArcsByCourier = {g: [] for g in courierGroups}
departureArcsByCourierAndRestaurant = defaultdict(list) # (c,r1): [timedArc1, timedArc2, ...]
arrivalArcsByCourierAndRestaurant = defaultdict(list) # (c,r2): [timedArc1, timedArc2, ...]
arcsByUntimedArc = {u: [] for u in untimedArcData}
waitingArcsByGroupRestaurant = defaultdict(list)





for arc in timedArcs:
    (c,r1,t1,s,r2,t2) = arc
    if t2 >= t1: # This condition is a hacky solution to the existence of incorrect arcs
        arcsByDepartureNode[c,r1,t1].append(arc)
        arcsByArrivalNode[c,r2,t2].append(arc)
        arcsByCourier[c].append(arc)
        departureArcsByCourierAndRestaurant[c,r1].append(arc)
        arrivalArcsByCourierAndRestaurant[c,r2].append(arc)
        for o in s:
            arcsByOrder[o].append(arc)
        if r1 == 0:
            outArcsByCourier[c].append(arc)
        if r1 != r2 or s != ():
            arcsByUntimedArc[c,s,r2].append(arc)
        if r1 == r2 and s == ():
            waitingArcsByGroupRestaurant[c,r1].append(arc)





arcsByDepartureNode = dict(arcsByDepartureNode)
arcsByArrivalNode = dict(arcsByArrivalNode)
arcsByCourier = dict(arcsByCourier)
departureArcsByCourierAndRestaurant = dict(departureArcsByCourierAndRestaurant)
arrivalArcsByCourierAndRestaurant = dict(arrivalArcsByCourierAndRestaurant)
waitingArcsByGroupRestaurant = dict(waitingArcsByGroupRestaurant)





arcs = {arc: m.addVar() for arc in timedArcs if arc[2] <= arc[5]}
doesThisCourierStart = {c: m.addVar() for c in courierData}
payments = {group: m.addVar() for group in courierGroups}





m.setObjective(quicksum(payments[c] for c in courierGroups))





flowConstraint = {node:
          m.addConstr(quicksum(arcs[arc] for arc in arcsByDepartureNode[node]) 
                      == quicksum(arcs[arc] for arc in arcsByArrivalNode[node])
          )
      for node in nodesInModel if node[1] != 0}
homeArcs = {c: m.addConstr(quicksum(arcs[arc] for arc in outArcsByCourier[c]) 
                           <= len(courierGroups[c][0])) for c in courierGroups}
deliverOrders = {o: m.addConstr(quicksum(arcs[arc] for arc in arcsByOrder[o]) 
                                == 1) for o in orderData}
arcsIffLeaveHome = {c: m.addConstr(
    quicksum(arcs[arc] for arc in arcsByCourier[c]) <= 
    quicksum(arcs[arc] for arc in outArcsByCourier[c]) * len(arcsByCourier[c])) 
    for c in courierGroups}
paidPerDelivery = {g: m.addConstr(payments[g] >= quicksum(arcs[arc] * len(arc[3]) * payPerDelivery for arc in arcsByCourier[g]) + quicksum((courierData[c][3] - courierData[c][2]) * minPayPerHour / 60 * (1-doesThisCourierStart[c]) for c in courierGroups[g][0])) for g in courierGroups}
paidPerTime = {c: m.addConstr(payments[c] >= quicksum((courierData[courier][3] - courierData[courier][2]) * minPayPerHour / 60 for courier in courierGroups[c][0])) for c in courierGroups}
courierStartsMatchesNumber = {g: m.addConstr(quicksum(doesThisCourierStart[c]
                                                      for c in courierGroups[g][0])
                                             == quicksum(arcs[arc] for arc in outArcsByCourier[g])
                                             ) for g in courierGroups}





# Code for doing all VIs:
VIConstraints = {}
for arc in untimedArcs:
    if arc[1] != (): # not an entry arc, do predecessor valid inequalities
        validPredecessorUntimedArcs = []
        leavingRestaurant, _, latestLeavingTime, _ = untimedArcData[arc]
        for untimedArc in untimedArcsByCourierNextRestaurant[(arc[0], leavingRestaurant)]:
            if untimedArcData[untimedArc][1] + untimedArcData[untimedArc][3] <= latestLeavingTime:
                if set(arc[1]) & set(untimedArc[1]) != set():
                    continue
                validPredecessorUntimedArcs.append(untimedArc)
        if len(validPredecessorUntimedArcs) == 0:
            print('No predecessor arcs', arc)
        VIConstraints[(0,arc,tuple(validPredecessorUntimedArcs))] = m.addConstr(quicksum(arcs[timedArc] for timedArc in arcsByUntimedArc[arc])
                    <= quicksum(arcs[timedArc] for timedArc in arcsByUntimedArc[untimedArc]
                                for untimedArc in validPredecessorUntimedArcs))
    if arc[2] != 0: # not an exit arc, do successor valid inequalities
        validSuccessorUntimedArcs = []
        _, earliestLeavingTime, _, travelTime = untimedArcData[arc]
        for untimedArc in untimedArcsByCourierRestaurant[(arc[0], arc[2])]:
            if untimedArcData[untimedArc][2] >= earliestLeavingTime + travelTime:
                if set(arc[1]) & set(untimedArc[1]) != set():
                    continue
                validSuccessorUntimedArcs.append(untimedArc)
        if len(validSuccessorUntimedArcs) == 0:
            print('No successor arcs', arc)
        VIConstraints[(1,arc,tuple(validSuccessorUntimedArcs))] = m.addConstr(quicksum(arcs[timedArc] for timedArc in arcsByUntimedArc[arc])
                    <= quicksum(arcs[timedArc] for timedArc in arcsByUntimedArc[untimedArc]
                                for untimedArc in validSuccessorUntimedArcs))





# Code for removing broken VIs:
extraConstraints = {}
constraintDict = {}
t = 0
while True:
    constraintsAdded = 0
    m.optimize()
    usedUntimedArcs = [] # (courierGroup, orderSequence, r2)
    for arc in arcs:
        if arcs[arc].x > 0.001: # arc was turned on
            if arc[1] != arc[4] or arc[3] != (): # not a waiting arc
                untimedArc = (arc[0], arc[3], arc[4])
                usedUntimedArcs.append(untimedArc)
    print()
    print(str(len(usedUntimedArcs)) + ' total arcs used')
    # eventually move the following into a function to go after the generation of 'usedUntimedArcs'?
    for arc in usedUntimedArcs: # (group, orderSequence, r2)
        if arc[1] != (): # not an entry arc, do predecessor valid inequalities
            validPredecessorUntimedArcs = []
            leavingRestaurant, _, latestLeavingTime, _ = untimedArcData[arc]
            for untimedArc in untimedArcsByCourierNextRestaurant[(arc[0], leavingRestaurant)]:
                if untimedArcData[untimedArc][1] + untimedArcData[untimedArc][3] <= latestLeavingTime:
                    if set(arc[1]) & set(untimedArc[1]) != set():
                        continue
                    validPredecessorUntimedArcs.append(untimedArc)
            if len(validPredecessorUntimedArcs) == 0:
                print('No predecessor arcs', arc)
            if sum(arcs[timedArc].x for timedArc in arcsByUntimedArc[arc]) \
                > sum(arcs[timedArc].x for timedArc in arcsByUntimedArc[untimedArc]
                    for untimedArc in validPredecessorUntimedArcs) + 0.01:
                constraintDict[t] = m.addConstr(quicksum(arcs[timedArc] for timedArc in arcsByUntimedArc[arc])
                            <= quicksum(arcs[timedArc] for timedArc in arcsByUntimedArc[untimedArc]
                                        for untimedArc in validPredecessorUntimedArcs))
                extraConstraints[t] = [1, arc, validPredecessorUntimedArcs]
                constraintsAdded += 1
                t += 1
        if arc[2] != 0: # not an exit arc, do successor valid inequalities
            validSuccessorUntimedArcs = []
            _, earliestLeavingTime, _, travelTime = untimedArcData[arc]
            for untimedArc in untimedArcsByCourierRestaurant[(arc[0], arc[2])]:
                if untimedArcData[untimedArc][2] >= earliestLeavingTime + travelTime:
                    if set(arc[1]) & set(untimedArc[1]) != set():
                        continue
                    validSuccessorUntimedArcs.append(untimedArc)
            if len(validSuccessorUntimedArcs) == 0:
                print('No successor arcs', arc)
            if sum(arcs[timedArc].x for timedArc in arcsByUntimedArc[arc]) \
                > sum(arcs[timedArc].x for timedArc in arcsByUntimedArc[untimedArc]
                    for untimedArc in validSuccessorUntimedArcs) + 0.01:
                constraintDict[t] = m.addConstr(quicksum(arcs[timedArc] for timedArc in arcsByUntimedArc[arc])
                            <= quicksum(arcs[timedArc] for timedArc in arcsByUntimedArc[untimedArc]
                                        for untimedArc in validSuccessorUntimedArcs))
                extraConstraints[t] = [2, arc, validSuccessorUntimedArcs]
                constraintsAdded += 1
                t += 1
    if constraintsAdded > 0:
        print('Added ' + str(constraintsAdded) + ' valid inequality constraints')
        print()
    else:
        print('No valid inequality constraints added')
        print()
        break
print('Time = ' + str(time() - programStartTime))





# def ComputeAndRemoveIllegalPaths(listOfArcs, courierGroup):
#     arcStats = {} # untimedArc: departureRestaurant, earliestDepartureTime, latestDepartureTime, durationOfTravel, arrivalRestaurant
#     for timedArc in listOfArcs:
#         _, departureRestaurant, _, orderSequence, arrivalRestaurant, _ = timedArc
#         newArc = (departureRestaurant, orderSequence, arrivalRestaurant)
#         if departureRestaurant == 0:
#             earliestArrivalTime = min(courierData[courier][2] + TravelTime(courierData[courier], restaurantData[arrivalRestaurant]) for courier in courierGroups[courierGroup][0]) + pickupServiceTime / 2
#             durationOfTravel = min(TravelTime(courierData[courier], restaurantData[arrivalRestaurant]) for courier in courierGroups[courierGroup][0]) + pickupServiceTime / 2
#             earliestDepartureTime = earliestArrivalTime - durationOfTravel
#             latestDepartureTime = courierGroups[group][1] - durationOfTravel
#         elif arrivalRestaurant == 0:
#             _, earliestDepartureTime, latestDepartureTime, durationOfTravel = sequenceData[orderSequence]
#         else:
#             _, earliestDepartureTime, latestDepartureTime, durationOfTravel = sequenceNextRestaurantData[orderSequence, arrivalRestaurant]
#         arcStats[newArc] = (departureRestaurant, earliestDepartureTime, latestDepartureTime, durationOfTravel, arrivalRestaurant)
#     arcsWithTheirPredecessors = defaultdict(list)
#     arcsWithTheirSuccessors = defaultdict(list)
#     for arc1, arc2 in itertools.combinations(arcStats, 2):
#         if arcStats[arc1][1] + arcStats[arc1][3] <= arcStats[arc2][2]: # arc1 arrive before arc2 leaves
#             if arcStats[arc1][4] == arcStats[arc2][0]: # arc1 arrival restaurant is arc2 departure restaurant
#                 arcsWithTheirPredecessors[arc2].append(arc1) # arc1 is a predecessor of arc2
#                 arcsWithTheirSuccessors[arc1].append(arc2)
#         if arcStats[arc2][1] + arcStats[arc2][3] <= arcStats[arc1][2]:
#             if arcStats[arc2][4] == arcStats[arc2][0]:
#                 arcsWithTheirPredecessors[arc1].append(arc2)
#                 arcsWithTheirSuccessors[arc2].append(arc1)
#     arcsWithTheirPredecessors = dict(arcsWithTheirPredecessors)
#     arcsWithTheirSuccessors = dict(arcsWithTheirSuccessors)
    
#     IPD = Model('Illegal Path Determination')
#     X = {(arc,successor): IPD.addVar(vtype=GRB.BINARY) for arc in arcsWithTheirSuccessors for successor in arcsWithTheirSuccessors[arc]}
#     T = {arc: IPD.addVar() for arc in arcStats}
#     leaveAfterEarlyTime = {arc: IPD.addConstr(T[arc] >= arcStats[arc][1]) for arc in arcStats}
#     leaveBeforeLateTime = {arc: IPD.addConstr(T[arc] <= arcStats[arc][2]) for arc in arcStats}
#     enoughTimeForBothArcs = {(i,j): IPD.addConstr(T[i]+arcStats[i][3] <= T[j]+(arcStats[i][2]+arcStats[i][3]-arcStats[j][1])*(1-X[i,j])) for (i,j) in X}
#     entryArcsUsedOnce = {i: IPD.addConstr(quicksum(X[i,j] for j in arcsWithTheirSuccessors[i]) == 1) for i in arcsWithTheirSuccessors}
#     exitArcsUsedOnce = {j: IPD.addConstr(quicksum(X[i,j] for i in arcsWithTheirPredecessors[j]) == 1) for j in arcsWithTheirPredecessors}
#     IPD.optimize()
#     if IPD.Status == GRB.INFEASIBLE:
#         IPD.computeIIS()
#         IISArcs = set()
#         for arc in leaveAfterEarlyTime:
#             if leaveAfterEarlyTime[arc].IISConstr:
#                 IISArcs.add(arc)
#         for arc in leaveBeforeLateTime:
#             if leaveBeforeLateTime[arc].IISConstr:
#                 IISArcs.add(arc)
#         for arc in entryArcsUsedOnce:
#             if entryArcsUsedOnce[arc].IISConstr:
#                 IISArcs.add(arc)
#         for arc in exitArcsUsedOnce:
#             if exitArcsUsedOnce[arc].IISConstr:
#                 IISArcs.add(arc)
#         # IISArcs = set(k for k in leaveAfterEarlyTime if leaveAfterEarlyTime[k].IISConstr)
#         # IISArcs.union(set(k for k in leaveBeforeLateTime if leaveBeforeLateTime[k].IISConstr))
#         # IISArcs.union(set(k for k in entryArcsUsedOnce if entryArcsUsedOnce[k].IISConstr))
#         # IISArcs.union(set(k for k in exitArcsUsedOnce if exitArcsUsedOnce[k].IISConstr))
#         for (i,j) in enoughTimeForBothArcs:
#             if enoughTimeForBothArcs[i,j].IISConstr:
#                 IISArcs.add(i)
#                 IISArcs.add(j)
#         successorUntimedArcs = set()
#         for arc in IISArcs:
#             for potSuccessor in untimedArcsByCourierRestaurant[arc[0], arc[2]]:
#                 if potSuccessor not in IISArcs and untimedArcData[potSuccessor][2] >= untimedArcData[arc][1] + untimedArcData[arc][3]:
#                     successorUntimedArcs.add(potSuccessor)
#         usedTimedArcs = []
#         for arc in IISArcs:
#             usedTimedArcs += arcsByUntimedArc[arc]
#         timedArcSuccessors = []
#         for arc in successorUntimedArcs:
#             timedArcSuccessors += arcsByUntimedArc[arc]
#         m.addConstr(quicksum(arc for arc in usedTimedArcs) <= len(usedTimedArcs) - 1 + quicksum(arc for arc in timedArcSuccessors))
#         return True
#     return False

# def RemoveInvalidRoutes():
#     usedArcs = {arc: arcs[arc].x for arc in arcs if arcs[arc].x > 0 and (arc[3] != () or arc[1] == 0)}
#     usedArcsByGroup = {g: [] for g in courierGroups}
#     for arc in usedArcs:
#         usedArcsByGroup[arc[0]].append(arc)
#     didAddNewConstraints = False
#     for group in courierGroups:
#         didAddNewConstraints = didAddNewConstraints or ComputeAndRemoveIllegalPaths(usedArcsByGroup[group], group)
#     return didAddNewConstraints

# for arc in arcs:
#     if arc[3] != ():
#         arcs[arc].vtype=GRB.BINARY

# m.optimize()

# print('Time = ' + str(time() - programStartTime))
