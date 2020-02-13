{***************************************************************************}
{                                                                           }
{           Generics.StateMachine                                           }
{                                                                           }
{           Copyright (C) Malcolm Groves                                    }
{                                                                           }
{           http://www.malcolmgroves.com                                    }
{                                                                           }
{                                                                           }
{***************************************************************************}
{                                                                           }
{  Licensed under the Apache License, Version 2.0 (the "License");          }
{  you may not use this file except in compliance with the License.         }
{  You may obtain a copy of the License at                                  }
{                                                                           }
{      http://www.apache.org/licenses/LICENSE-2.0                           }
{                                                                           }
{  Unless required by applicable law or agreed to in writing, software      }
{  distributed under the License is distributed on an "AS IS" BASIS,        }
{  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. }
{  See the License for the specific language governing permissions and      }
{  limitations under the License.                                           }
{                                                                           }
{***************************************************************************}

unit Generics.StateMachine;

interface

uses
  System.SysUtils, Generics.Collections, Generics.Nullable;

{ TODO : What should happen if you add a Guard, OnEntry or OnExit and there is
  already one? Fail, or maintain a list? }
{ TODO : GuardProc and TransitionProc should take generic parameters that
  describe the states/triggers involved }

type
  EStateMachineException = class(Exception);
  EGuardFailure = class(EStateMachineException);
  EUnknownTrigger = class(EStateMachineException);
  EUnknownState = class(EStateMachineException);
  EInvalidStateMachine = class(EStateMachineException);

  TGuardProc = function (Sender: TObject) : Boolean of object;// reference to function : Boolean;
  TTransitionProc = procedure (Sender: TObject) of object;//reference to procedure;
  TTimeoutProc = procedure (Sender: TObject; ATimeOutIndex: Integer; var AIgnore: Boolean) of object;

  TTriggerHolder<TState, TTrigger> = class
  strict private
    FTrigger: TTrigger;
    FDestination: TState;
    FGuard: TGuardProc;
  public
    constructor Create(ATrigger: TTrigger; ADestination: TState;
      AGuard: TGuardProc = nil); virtual;
    function CanExecute: Boolean;
    property Destination: TState read FDestination;
  end;

  TStateMachine<TState, TTrigger> = class;

  TTStateHolder<TState, TTrigger> = class
  strict private
    //Added By DsLin --Begin
    type
      TTimeoutRec = record
        FTimeOut: Cardinal;    //毫秒，超时时间；0表示永远不超时
        FOnTimeOut: TTimeoutProc;  //当超时执行的函数(先执行本函数，再执行FOnExit)
        FToStateOnTimeOut: TState;    //超时后转向的状态
      end;
    //--End
  strict private
    FTriggers: TObjectDictionary<TTrigger, TTriggerHolder<TState, TTrigger>>;
    FState: TState;
    FStateMachine: TStateMachine<TState, TTrigger>;

    //Added By DsLin --Begin
    FStartTime: Cardinal;  //毫秒
    fTimeoutRecArr: array of TTimeoutRec;
    FSubStateMachine: TObject;  //子状态机
    //--End

    FOnEntry: TTransitionProc;
    FOnExit: TTransitionProc;

    function GetTriggerCount: Integer;
  protected
    procedure Enter;
    procedure Exit;
    procedure DoTimeOut;
  public
    constructor Create(AStateMachine: TStateMachine<TState, TTrigger>;
      AState: TState); virtual;
    destructor Destroy; override;
    function Trigger(ATrigger: TTrigger; ADestination: TState;
      AGuard: TGuardProc = nil): TTStateHolder<TState, TTrigger>;
    function OnEntry(AOnEntry: TTransitionProc)
      : TTStateHolder<TState, TTrigger>;
    function OnExit(AOnExit: TTransitionProc)
      : TTStateHolder<TState, TTrigger>;

      {
    function SetTimeOut(ATimeOutMilli: Cardinal; AOnTimeOut: TTimeoutProc;
      AToNewState: TState): TTStateHolder<TState, TTrigger>; overload; //仅需要设置一个超时事件；或者是多个但是不关心超时事件的序号
      }
    function SetTimeOut(ATimeOutMilli: Cardinal; AOnTimeOut: TTimeoutProc;
      AToNewState: TState; var AIndex: Integer): TTStateHolder<TState, TTrigger>; //可以设置多个超时事件


    function Initial: TTStateHolder<TState, TTrigger>;  //把本State设置为StateMachine的起始状态
    procedure Execute(ATrigger: TTrigger);
    function TriggerExists(ATrigger: TTrigger) : Boolean;

    property TriggerCount: Integer read GetTriggerCount;
    property State: TState read FState;
    property SubStateMachine: TObject read FSubStateMachine write FSubStateMachine;   //子状态机
  end;

  /// <summary>
  /// TStateMachine is a simple state machine that uses generic types to
  /// specify the different possible states and also the triggers that
  /// transition between the states.
  /// </summary>
  /// <typeparam name="TState">
  /// The type you wish to use to爏pecify the different possible states of
  /// your state machine.
  /// </typeparam>
  /// <typeparam name="TTrigger">
  /// The type you wish to use to爏pecify the different triggers in your
  /// state machine. A trigger is how you tell the state machine to
  /// transition from one state to another.
  /// </typeparam>
  TStateMachine<TState, TTrigger> = class
  strict private
    fBASE_TIME: Cardinal;  //
    FStates: TObjectDictionary<TState, TTStateHolder<TState, TTrigger>>;
    FCurrentState: TState;
    FInitialState: TNullable<TState>;
    FActive: Boolean;

    function GetStateCount: Integer;
    procedure SetActive(const Value: Boolean);
    function GetInitialState: TTStateHolder<TState, TTrigger>;
    function GetCurrentState: TTStateHolder<TState, TTrigger>;
  private
    function GetMilliNow: Cardinal;
  protected
    procedure TransitionToState(const AState: TState;
      AFirstTime: Boolean = False);
    procedure SetInitialState(const AState: TState);
  public
    constructor Create; virtual;
    destructor Destroy; override;
    /// <summary>
    /// Add a new state to the state machine.
    /// </summary>
    /// <param name="AState">
    /// The state you wish to have added.
    /// </param>
    /// <returns>
    /// Returns a TTStateCaddy for the state specified in the AState
    /// parameter.
    /// </returns>
    function State(AState: TState): TTStateHolder<TState, TTrigger>;

    procedure CheckCurrentStateTimeOut;  //一般是在线程中进行调用检查是否超时，注意：需要用Try Except 结构来抓获异常

    property StateCount: Integer read GetStateCount;
    property CurrentState: TTStateHolder<TState, TTrigger>
      read GetCurrentState;
    property InitialState: TTStateHolder<TState, TTrigger>
      read GetInitialState;
    property Active: Boolean read FActive write SetActive;
  end;

implementation

uses System.DateUtils, WinApi.Windows;

{ TTriggerCaddy<TState, TTrigger> }

function TTriggerHolder<TState, TTrigger>.CanExecute: Boolean;
begin
  if Assigned(FGuard) then
    Result := FGuard(Self)
  else
    Result := True;
end;

constructor TTriggerHolder<TState, TTrigger>.Create(ATrigger: TTrigger;
  ADestination: TState; AGuard: TGuardProc);
begin
  inherited Create;
  FTrigger := ATrigger;
  FDestination := ADestination;
  FGuard := AGuard;
end;

{ TTStateCaddy<TState, TTrigger> }

function TTStateHolder<TState, TTrigger>.Trigger(ATrigger: TTrigger;
  ADestination: TState; AGuard: TGuardProc): TTStateHolder<TState, TTrigger>;
var
  LConfiguredTrigger: TTriggerHolder<TState, TTrigger>;
begin
  LConfiguredTrigger := TTriggerHolder<TState, TTrigger>.Create(ATrigger,
    ADestination, AGuard);
  FTriggers.Add(ATrigger, LConfiguredTrigger);
  Result := Self;
end;

constructor TTStateHolder<TState, TTrigger>.Create(AStateMachine
  : TStateMachine<TState, TTrigger>; AState: TState);
begin
  inherited Create;
  FStateMachine := AStateMachine;
  FTriggers := TObjectDictionary < TTrigger, TTriggerHolder < TState,
    TTrigger >>.Create([doOwnsValues]);
  FState := AState;
  FStartTime := 0;  //表示还没有设置这个运行起始时间
  SetLength(FTimeoutRecArr, 0);
end;

destructor TTStateHolder<TState, TTrigger>.Destroy;
begin
  FreeAndNil(FTriggers);
  inherited;
end;

procedure TTStateHolder<TState, TTrigger>.DoTimeOut;
var
  i, iCnt: Integer;
  Ignore: Boolean;
begin
  if not FStateMachine.Active then
    raise EStateMachineException.Create('FSM: StateMachine not active');

  iCnt := Length(FTimeOutRecArr);
  if fStartTime = 0 then
    fStartTime := Self.fStateMachine.GetMilliNow()
  else if iCnt > 0 then begin
    for i := 0 to iCnt - 1 do begin
      if (FTimeOutRecArr[i].FTimeOut > 0) and (Self.fStateMachine.GetMilliNow() - fStartTime >= FTimeOutRecArr[i].FTimeOut) then begin
        Ignore := False;
        if Assigned(FTimeOutRecArr[i].FOnTimeOut) then begin
          FTimeOutRecArr[i].FOnTimeOut(Self, i, Ignore);
          if Ignore then
            Continue;
        end;
        FStateMachine.TransitionToState(FTimeOutRecArr[i].FToStateOnTimeOut);
        Break;  //每一次仅仅执行一个超时的事件
      end;
    end;
  end;
end;

procedure TTStateHolder<TState, TTrigger>.Enter;
begin
  Self.FStartTime := Self.FStateMachine.GetMilliNow();
  if Assigned(FOnEntry) then
    FOnEntry(Self);
end;

procedure TTStateHolder<TState, TTrigger>.Execute(ATrigger: TTrigger);
var
  LTrigger: TTriggerHolder<TState, TTrigger>;
begin
  if not FStateMachine.Active then
    raise EStateMachineException.Create('FSM: StateMachine not active');

  if not FTriggers.TryGetValue(ATrigger, LTrigger) then
    raise EUnknownTrigger.Create('FSM: Requested Trigger not found');

  if not LTrigger.CanExecute then
    raise EGuardFailure.Create('FSM: Guard on trigger prevented execution');

  FStateMachine.TransitionToState(LTrigger.Destination);
end;

procedure TTStateHolder<TState, TTrigger>.Exit;
begin
  if not FStateMachine.Active then
    raise EStateMachineException.Create('FSM: StateMachine not active');

  if Assigned(FOnExit) then
    FOnExit(Self);
end;

function TTStateHolder<TState, TTrigger>.GetTriggerCount: Integer;
begin
  if Assigned(FTriggers) then
    Result := FTriggers.Count;
end;

function TTStateHolder<TState, TTrigger>.Initial
  : TTStateHolder<TState, TTrigger>;
begin
  FStateMachine.SetInitialState(FState);
  Result := Self;
end;

function TTStateHolder<TState, TTrigger>.TriggerExists(
  ATrigger: TTrigger): Boolean;
var
  LTrigger: TTriggerHolder<TState, TTrigger>;
begin
  Result := FTriggers.TryGetValue(ATrigger, LTrigger);
end;

function TTStateHolder<TState, TTrigger>.OnEntry(AOnEntry: TTransitionProc)
  : TTStateHolder<TState, TTrigger>;
begin
  FOnEntry := AOnEntry;
  Result := Self;
end;

function TTStateHolder<TState, TTrigger>.OnExit(AOnExit: TTransitionProc)
  : TTStateHolder<TState, TTrigger>;
begin
  FOnExit := AOnExit;
  Result := Self;
end;

{
function TTStateHolder<TState, TTrigger>.SetTimeOut(ATimeOutMilli: Cardinal;
  AOnTimeOut: TTimeoutProc; AToNewState: TState): TTStateHolder<TState, TTrigger>;
var
  Inx: Integer;
begin
  Result :=SetTimeOut(ATimeOutMilli, AOnTimeOut, AToNewState, Inx);
end;
}
function TTStateHolder<TState, TTrigger>.SetTimeOut(ATimeOutMilli: Cardinal;
  AOnTimeOut: TTimeoutProc; AToNewState: TState; var AIndex: Integer): TTStateHolder<TState, TTrigger>;
begin
  SetLength(FTimeoutRecArr, Length(FTimeoutRecArr) + 1);
  AIndex := High(FTimeoutRecArr);
  FTimeoutRecArr[AIndex].FTimeOut := ATimeOutMilli; //毫秒，超时时间；0表示永远不超时
  FTimeoutRecArr[AIndex].FOnTimeOut := AOnTimeOut;  //超时时执行的函数(先执行本函数，再执行FOnExit)
  FTimeoutRecArr[AIndex].FToStateOnTimeOut := AToNewState;    //超时后转向的状态

  Result := Self;
end;

procedure TStateMachine<TState, TTrigger>.CheckCurrentStateTimeOut;
begin
  if fActive then begin
    CurrentState.DoTimeOut;
  end;
end;

constructor TStateMachine<TState, TTrigger>.Create;
begin
  inherited Create;
  FStates := TObjectDictionary <TState, TTStateHolder<TState, TTrigger>>.Create([doOwnsValues]);
  fBASE_TIME := Winapi.Windows.GetTickCount;
end;

destructor TStateMachine<TState, TTrigger>.Destroy;
begin
  Active := False;
  FStates.Free;
  inherited;
end;

function TStateMachine<TState, TTrigger>.GetCurrentState
  : TTStateHolder<TState, TTrigger>;
var
  LCurrentState: TTStateHolder<TState, TTrigger>;
begin
  if not FStates.TryGetValue(FCurrentState, LCurrentState) then
    raise EUnknownState.Create('FSM: Unable to find Current State');

  Result := LCurrentState;
end;

function TStateMachine<TState, TTrigger>.GetInitialState
  : TTStateHolder<TState, TTrigger>;
var
  LInitialState: TTStateHolder<TState, TTrigger>;
begin
  if not FInitialState.HasValue then
    raise EInvalidStateMachine.Create('FSM: StateMachine has not initial state');

  if not FStates.TryGetValue(FInitialState, LInitialState) then
    raise EUnknownState.Create('FSM: Unable to find Initial State');

  Result := LInitialState;
end;

function TStateMachine<TState, TTrigger>.GetMilliNow: Cardinal;
begin
  Result := Winapi.Windows.GetTickCount - fBASE_TIME; //精度在16MS左右，每47天左右会归零，写服务程序需要特别注意
end;

function TStateMachine<TState, TTrigger>.GetStateCount: Integer;
begin
  if Assigned(FStates) then
    Result := FStates.Count;
end;

procedure TStateMachine<TState, TTrigger>.SetActive(const Value: Boolean);
begin
  if FActive <> Value then begin
    if Value and not FInitialState.HasValue then
      raise EInvalidStateMachine.Create('FSM: StateMachine has no initial state specified');

    FActive := Value;
    if FActive then
      TransitionToState(FInitialState, True);
  end;
end;

procedure TStateMachine<TState, TTrigger>.SetInitialState(const AState: TState);
begin
  if FInitialState.HasValue then
    raise EInvalidStateMachine.Create('FSM: StatMachine cannot have two Initial States');

  FInitialState := AState;
end;

procedure TStateMachine<TState, TTrigger>.TransitionToState
  (const AState: TState; AFirstTime: Boolean);
begin
  if not Active then
    raise EStateMachineException.Create('FSM: StateMachine not active');

  if not FStates.ContainsKey(AState) then
    raise EUnknownState.Create('FSM: Unable to find Configured State');

  // only exit if not the first transition to initial state
  if not AFirstTime then
    CurrentState.Exit;

  FCurrentState := AState;

  CurrentState.Enter;

end;

function TStateMachine<TState, TTrigger>.State(AState: TState)
  : TTStateHolder<TState, TTrigger>;
begin
  Result := TTStateHolder<TState, TTrigger>.Create(Self, AState);
  FStates.Add(AState, Result);
end;

end.

