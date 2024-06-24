// automatically generated by the FlatBuffers compiler, do not modify

/* eslint-disable @typescript-eslint/no-unused-vars, @typescript-eslint/no-explicit-any, @typescript-eslint/no-non-null-assertion */

import { Monster as MyGame_Example2_Monster, MonsterT as MyGame_Example2_MonsterT } from '../../my-game/example2/monster.ts';
import { Monster, MonsterT } from '../../my-game/example/monster.ts';
import { TestSimpleTableWithEnum, TestSimpleTableWithEnumT } from '../../my-game/example/test-simple-table-with-enum.ts';


export enum AnyUniqueAliases {
  NONE = 0,
  M = 1,
  TS = 2,
  M2 = 3
}

export function unionToAnyUniqueAliases(
  type: AnyUniqueAliases,
  accessor: (obj:Monster|MyGame_Example2_Monster|TestSimpleTableWithEnum) => Monster|MyGame_Example2_Monster|TestSimpleTableWithEnum|null
): Monster|MyGame_Example2_Monster|TestSimpleTableWithEnum|null {
  switch(AnyUniqueAliases[type]) {
    case 'NONE': return null; 
    case 'M': return accessor(new Monster())! as Monster;
    case 'TS': return accessor(new TestSimpleTableWithEnum())! as TestSimpleTableWithEnum;
    case 'M2': return accessor(new MyGame_Example2_Monster())! as MyGame_Example2_Monster;
    default: return null;
  }
}

export function unionListToAnyUniqueAliases(
  type: AnyUniqueAliases, 
  accessor: (index: number, obj:Monster|MyGame_Example2_Monster|TestSimpleTableWithEnum) => Monster|MyGame_Example2_Monster|TestSimpleTableWithEnum|null, 
  index: number
): Monster|MyGame_Example2_Monster|TestSimpleTableWithEnum|null {
  switch(AnyUniqueAliases[type]) {
    case 'NONE': return null; 
    case 'M': return accessor(index, new Monster())! as Monster;
    case 'TS': return accessor(index, new TestSimpleTableWithEnum())! as TestSimpleTableWithEnum;
    case 'M2': return accessor(index, new MyGame_Example2_Monster())! as MyGame_Example2_Monster;
    default: return null;
  }
}
