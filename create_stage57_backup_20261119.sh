#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
python3 - <<'PY'
import base64, zlib, pathlib, zipfile, hashlib, subprocess, tempfile, json, os, datetime
ROOT=pathlib.Path.cwd()
name='公理研究_第57段階_20261119_GitHub研究バックアップ.zip'
out=ROOT/name
report=zlib.decompress(base64.b64decode('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')).decode('utf-8')
EXCLUDE_DIRS={'.git','__pycache__','.venv','venv','.mypy_cache','.pytest_cache','.ipynb_checkpoints','node_modules'}
EXCLUDE_SUFFIXES={'.vo','.vos','.vok','.glob','.aux','.pyc','.swp','.swo'}
EXCLUDE_NAMES={name,name+'.sha256'}

def git(*args):
    p=subprocess.run(['git',*args],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False)
    return (p.returncode, p.stdout.decode('utf-8','replace'),p.stderr.decode('utf-8','replace'))

with tempfile.TemporaryDirectory(prefix='stage57_fullbackup_') as tmp:
    tmp=pathlib.Path(tmp)
    bundle=tmp/'git_history_all_refs.bundle'
    r=subprocess.run(['git','bundle','create',str(bundle),'--all'],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    if r.returncode != 0:
        raise RuntimeError('Git履歴bundle生成失敗: '+r.stderr.decode('utf-8','replace'))
    status=git('status','--short','--untracked-files=all')[1]
    branch=git('branch','-avv')[1]
    log=git('log','--all','--date=iso-strict','--pretty=format:%H %ad %s','-n','100')[1]
    diff=git('diff','--binary')[1]
    staged=git('diff','--cached','--binary')[1]
    files=[]
    for dirpath,dirnames,filenames in os.walk(ROOT):
        dirnames[:]=sorted(d for d in dirnames if d not in EXCLUDE_DIRS)
        base=pathlib.Path(dirpath)
        for filename in sorted(filenames):
            p=base/filename
            if p.is_symlink() or filename in EXCLUDE_NAMES or p.suffix in EXCLUDE_SUFFIXES:
                continue
            if p.is_file():
                files.append(p)
    sha_lines=[]
    entries=[]
    with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6,allowZip64=True) as z:
        for p in files:
            arc='worktree/'+p.relative_to(ROOT).as_posix()
            z.write(p,arc)
            h=hashlib.sha256()
            with p.open('rb') as f:
                for chunk in iter(lambda:f.read(1024*1024),b''): h.update(chunk)
            digest=h.hexdigest()
            sha_lines.append(digest+'  '+arc)
            entries.append({'path':arc,'bytes':p.stat().st_size,'sha256':digest})
        z.write(bundle,'git_history_all_refs.bundle')
        z.writestr('audit/第57段階_20261119_研究成果_監査_明日レジメ.md',report)
        z.writestr('audit/git_status_short.txt',status)
        z.writestr('audit/git_branches.txt',branch)
        z.writestr('audit/git_log_100.txt',log+'\n')
        z.writestr('audit/git_worktree_diff.patch',diff)
        z.writestr('audit/git_index_diff.patch',staged)
        z.writestr('audit/worktree_sha256.txt','\n'.join(sha_lines)+'\n')
        z.writestr('audit/worktree_manifest.json',json.dumps({'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_directory':str(ROOT),'file_count':len(files),'files':entries},ensure_ascii=False,indent=2))
        z.writestr('audit/README_検査方法.txt',
          '研究ソースの作業ツリーとGit全履歴bundleの保存。git未追跡ファイルも収録。\n'
          'Coq生成物(.vo/.vos/.vok/.glob/.aux)、Git作業用内部ディレクトリ.git、cacheは除外。\n'
          '従って、作業ディレクトリをバイト単位で完全複製したものではない。\n'
          '作業ツリーはworktree/、Git履歴はgit_history_all_refs.bundle。\n'
          '各ファイルのSHA256はaudit/worktree_sha256.txt。\n'
          'Git履歴の復元例: git clone git_history_all_refs.bundle <new-directory>\n'
          'このコマンドはリポジトリを変更したりgit commit/pushしたりしない。\n'
          'iCloud保存は利用者がiPad「ファイル」アプリから行い、存在を確認する。\n')
    with zipfile.ZipFile(out,'r') as z:
        bad=z.testzip()
        if bad: raise RuntimeError('ZIP検証失敗: '+str(bad))
    digest=hashlib.sha256(out.read_bytes()).hexdigest() if out.stat().st_size < 50_000_000 else None
    if digest is None:
        h=hashlib.sha256()
        with out.open('rb') as f:
            for chunk in iter(lambda:f.read(4*1024*1024),b''):h.update(chunk)
        digest=h.hexdigest()
    (ROOT/(name+'.sha256')).write_text(digest+'  '+name+'\n',encoding='utf-8')
    print('バックアップZIP作成・ZIP検証成功')
    print('ZIP:',out.name,'bytes=',out.stat().st_size)
    print('Git履歴bundle: 収録済み')
    print('収録した作業ツリーファイル:',len(files))
    print('未追跡を含むgit status:')
    print(status or '(変更なし)')
    print('SHA256:',digest)
    print('次: VS Code ExplorerでZIPをダウンロードし、iPadの「ファイル」→「iCloud Drive」に保存してください。')
PY
